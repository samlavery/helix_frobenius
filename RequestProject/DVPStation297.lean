import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 297` (rung-309; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT297 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((297 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-19999/50000 : ℚ) : ℝ))

theorem st297_c1 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((921069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19999/200000) (δ := 1/1000000000) (ψ := -19999/50000) 297 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t1 : ((920969/1000000 : ℚ) : ℝ) ≤ stT297 1 := by
  have hc : ((920969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((920969/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((920969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c2 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((117737/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2701079/10000000) (δ := 2973/200000000) (ψ := -19999/50000) 297 33
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t2 : ((52021839919/156250000000 : ℚ) : ℝ) ≤ stT297 2 := by
  have hc : ((7357/15625 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52021839919/156250000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((7357/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c3 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((199857/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5909/625000) (δ := 599/40000000) (ψ := -19999/50000) 297 52
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t3 : ((576879659587/1000000000000 : ℚ) : ℝ) ≤ stT297 3 := by
  have hc : ((199837/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((576879659587/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((199837/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c4 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-209011/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6402071/10000000) (δ := 933/62500000) (ψ := -19999/50000) 297 66
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t4 : ((-261295052259/625000000000 : ℚ) : ℝ) ≤ stT297 4 := by
  have hc : ((-52259/62500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261295052259/625000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-52259/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c5 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((127281/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110121/500000) (δ := 15047/1000000000) (ψ := -19999/50000) 297 76
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t5 : ((113825674447/400000000000 : ℚ) : ℝ) ≤ stT297 5 := by
  have hc : ((127261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113825674447/400000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((127261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c6 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((26279/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237221/625000) (δ := 233/15625000) (ψ := -19999/50000) 297 85
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t6 : ((53539710189/2500000000000 : ℚ) : ℝ) ≤ stT297 6 := by
  have hc : ((26229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53539710189/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((26229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c7 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((60027/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44101/625000) (δ := 7481/500000000) (ψ := -19999/50000) 297 92
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t7 : ((226857067613/625000000000 : ℚ) : ℝ) ≤ stT297 7 := by
  have hc : ((240083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226857067613/625000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((240083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c8 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-310949/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5604901/10000000) (δ := 3001/200000000) (ψ := -19999/50000) 297 98
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t8 : ((-549773769233/2500000000000 : ℚ) : ℝ) ≤ stT297 8 := by
  have hc : ((-310999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549773769233/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-310999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c9 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((444509/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1189001/10000000) (δ := 1881/125000000) (ψ := -19999/50000) 297 104
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t9 : ((1481529851847/5000000000000 : ℚ) : ℝ) ≤ stT297 9 := by
  have hc : ((444459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1481529851847/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((444459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c10 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((825641/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1498647/10000000) (δ := 15019/1000000000) (ψ := -19999/50000) 297 109
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t10 : ((2610589316857/10000000000000 : ℚ) : ℝ) ≤ stT297 10 := by
  have hc : ((825541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2610589316857/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((825541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c11 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-843697/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1609331/2500000) (δ := 14913/1000000000) (ψ := -19999/50000) 297 113
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t11 : ((-1272072073929/5000000000000 : ℚ) : ℝ) ≤ stT297 11 := by
  have hc : ((-843797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1272072073929/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-843797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c12 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-247449/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -468533/625000) (δ := 7427/500000000) (ψ := -19999/50000) 297 118
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t12 : ((-11162438507/39062500000 : ℚ) : ℝ) ≤ stT297 12 := by
  have hc : ((-123737/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11162438507/39062500000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-123737/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c13 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-86597/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4811287/10000000) (δ := 1487/100000000) (ψ := -19999/50000) 297 121
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t13 : ((-120123101811/1250000000000 : ℚ) : ℝ) ≤ stT297 13 := by
  have hc : ((-43311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120123101811/1250000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-43311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c14 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((364081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187211/625000) (δ := 14899/1000000000) (ψ := -19999/50000) 297 125
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t14 : ((243194997093/2500000000000 : ℚ) : ℝ) ≤ stT297 14 := by
  have hc : ((363981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243194997093/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((363981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c15 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((903391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 553981/5000000) (δ := 14983/1000000000) (ψ := -19999/50000) 297 128
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t15 : ((583071630627/2500000000000 : ℚ) : ℝ) ≤ stT297 15 := by
  have hc : ((903291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583071630627/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((903291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c16 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((361879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1903909/10000000) (δ := 7471/500000000) (ψ := -19999/50000) 297 131
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t16 : ((361829/2000000 : ℚ) : ℝ) ≤ stT297 16 := by
  have hc : ((361829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361829/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((361829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c17 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((4983/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25777/1250000) (δ := 15039/1000000000) (ψ := -19999/50000) 297 134
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t17 : ((1208433627/5000000000 : ℚ) : ℝ) ≤ stT297 17 := by
  have hc : ((1993/2000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1208433627/5000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((1993/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c18 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-75149/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4889993/10000000) (δ := 2997/200000000) (ψ := -19999/50000) 297 137
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t18 : ((-177175061887/2000000000000 : ℚ) : ℝ) ≤ stT297 18 := by
  have hc : ((-75169/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177175061887/2000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-75169/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c19 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((35199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29992/78125) (δ := 1863/125000000) (ψ := -19999/50000) 297 139
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t19 : ((80522616543/10000000000000 : ℚ) : ℝ) ≤ stT297 19 := by
  have hc : ((35099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80522616543/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((35099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c20 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-121839/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2599819/5000000) (δ := 15021/1000000000) (ψ := -19999/50000) 297 142
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t20 : ((-8515505961/78125000000 : ℚ) : ℝ) ≤ stT297 20 := by
  have hc : ((-15233/31250 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8515505961/78125000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-15233/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c21 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((987929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388841/10000000) (δ := 3007/200000000) (ψ := -19999/50000) 297 144
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t21 : ((1077809355781/5000000000000 : ℚ) : ℝ) ≤ stT297 21 := by
  have hc : ((987829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1077809355781/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((987829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c22 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((229231/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 684083/2500000) (δ := 14853/1000000000) (ψ := -19999/50000) 297 146
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t22 : ((488615496267/5000000000000 : ℚ) : ℝ) ≤ stT297 22 := by
  have hc : ((229181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488615496267/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((229181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c23 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-79437/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4325867/10000000) (δ := 929/62500000) (ψ := -19999/50000) 297 148
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t23 : ((-33148384123/1000000000000 : ℚ) : ℝ) ≤ stT297 23 := by
  have hc : ((-79487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33148384123/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-79487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c24 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-57817/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4510443/10000000) (δ := 601/40000000) (ψ := -19999/50000) 297 150
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t24 : ((-29517379941/625000000000 : ℚ) : ℝ) ≤ stT297 24 := by
  have hc : ((-28921/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29517379941/625000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-28921/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c25 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((10367/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 851213/2500000) (δ := 14893/1000000000) (ψ := -19999/50000) 297 152
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t25 : ((5181/125000 : ℚ) : ℝ) ≤ stT297 25 := by
  have hc : ((5181/25000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5181/125000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((5181/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c26 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((90299/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222059/2000000) (δ := 931/62500000) (ψ := -19999/50000) 297 154
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t26 : ((177071265529/1000000000000 : ℚ) : ℝ) ≤ stT297 26 := by
  have hc : ((90289/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177071265529/1000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((90289/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c27 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((611071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2283459/10000000) (δ := 14981/1000000000) (ψ := -19999/50000) 297 156
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t27 : ((2351627379/20000000000 : ℚ) : ℝ) ≤ stT297 27 := by
  have hc : ((610971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2351627379/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((610971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c28 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-111837/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418523/625000) (δ := 14867/1000000000) (ψ := -19999/50000) 297 158
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t28 : ((-422751515277/2500000000000 : ℚ) : ℝ) ≤ stT297 28 := by
  have hc : ((-223699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422751515277/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-223699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c29 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((110189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3650959/10000000) (δ := 743/50000000) (ψ := -19999/50000) 297 159
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t29 : ((204430098817/10000000000000 : ℚ) : ℝ) ≤ stT297 29 := by
  have hc : ((110089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204430098817/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((110089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c30 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((508597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162069/625000) (δ := 7473/500000000) (ψ := -19999/50000) 297 161
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t30 : ((928383821277/10000000000000 : ℚ) : ℝ) ≤ stT297 30 := by
  have hc : ((508497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((928383821277/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((508497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c31 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-749547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3022717/5000000) (δ := 2993/200000000) (ψ := -19999/50000) 297 162
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t31 : ((-673203246469/5000000000000 : ℚ) : ℝ) ≤ stT297 31 := by
  have hc : ((-749647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-673203246469/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-749647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c32 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((30103/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1797083/10000000) (δ := 14879/1000000000) (ψ := -19999/50000) 297 164
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t32 : ((26603994417/200000000000 : ℚ) : ℝ) ≤ stT297 32 := by
  have hc : ((30099/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26603994417/200000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((30099/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c33 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-134139/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5342867/10000000) (δ := 7493/500000000) (ψ := -19999/50000) 297 165
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t33 : ((-58387401357/625000000000 : ℚ) : ℝ) ≤ stT297 33 := by
  have hc : ((-33541/62500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58387401357/625000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-33541/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c34 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((7913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907207/10000000) (δ := 3/200000) (ψ := -19999/50000) 297 167
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t34 : ((2679835561/2000000000000 : ℚ) : ℝ) ≤ stT297 34 := by
  have hc : ((7813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2679835561/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((7813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c35 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((361307/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119253/625000) (δ := 2979/200000000) (ψ := -19999/50000) 297 168
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t35 : ((152658899289/1250000000000 : ℚ) : ℝ) ≤ stT297 35 := by
  have hc : ((361257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152658899289/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((361257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c36 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-47843/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3558489/5000000) (δ := 1861/125000000) (ψ := -19999/50000) 297 169
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t36 : ((-9968335327/62500000000 : ℚ) : ℝ) ≤ stT297 36 := by
  have hc : ((-5981/6250 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9968335327/62500000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-5981/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c37 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-141/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3955191/10000000) (δ := 7437/500000000) (ψ := -19999/50000) 297 171
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t37 : ((-93543031/50000000000 : ℚ) : ℝ) ≤ stT297 37 := by
  have hc : ((-569/50000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93543031/50000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-569/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c38 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((998477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1078/78125) (δ := 14967/1000000000) (ψ := -19999/50000) 297 172
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t38 : ((809790573339/5000000000000 : ℚ) : ℝ) ≤ stT297 38 := by
  have hc : ((998377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((809790573339/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((998377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c39 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((16793/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371683/1000000) (δ := 467/31250000) (ψ := -19999/50000) 297 173
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t39 : ((26858286213/2000000000000 : ℚ) : ℝ) ≤ stT297 39 := by
  have hc : ((16773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26858286213/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((16773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c40 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-182727/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6807333/10000000) (δ := 3713/250000000) (ψ := -19999/50000) 297 174
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t40 : ((-288948408833/2000000000000 : ℚ) : ℝ) ≤ stT297 40 := by
  have hc : ((-182747/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288948408833/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-182747/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c41 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-201733/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3137169/5000000) (δ := 2973/200000000) (ψ := -19999/50000) 297 176
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t41 : ((-78773283851/625000000000 : ℚ) : ℝ) ≤ stT297 41 := by
  have hc : ((-100879/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78773283851/625000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-100879/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c42 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-65091/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4089833/10000000) (δ := 3743/250000000) (ψ := -19999/50000) 297 177
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t42 : ((-50295964747/5000000000000 : ℚ) : ℝ) ≤ stT297 42 := by
  have hc : ((-65191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50295964747/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-65191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c43 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((119477/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727/3125) (δ := 14979/1000000000) (ψ := -19999/50000) 297 178
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t43 : ((36434026629/400000000000 : ℚ) : ℝ) ≤ stT297 43 := by
  have hc : ((119457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36434026629/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((119457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c44 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((463237/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48233/500000) (δ := 3729/250000000) (ψ := -19999/50000) 297 179
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t44 : ((174570085243/1250000000000 : ℚ) : ℝ) ≤ stT297 44 := by
  have hc : ((463187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174570085243/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((463187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c45 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((499993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13431/10000000) (δ := 7447/500000000) (ψ := -19999/50000) 297 180
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t45 : ((745270529473/5000000000000 : ℚ) : ℝ) ≤ stT297 45 := by
  have hc : ((499943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((745270529473/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((499943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c46 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((242233/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 624801/10000000) (δ := 14901/1000000000) (ψ := -19999/50000) 297 181
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t46 : ((11159877411/78125000000 : ℚ) : ℝ) ≤ stT297 46 := by
  have hc : ((15138/15625 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11159877411/78125000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((15138/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c47 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((937957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177053/2000000) (δ := 2999/200000000) (ψ := -19999/50000) 297 182
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t47 : ((1368004175193/10000000000000 : ℚ) : ℝ) ≤ stT297 47 := by
  have hc : ((937857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1368004175193/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((937857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c48 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((948039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202363/2500000) (δ := 3003/200000000) (ψ := -19999/50000) 297 183
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t48 : ((10945851633/80000000000 : ℚ) : ℝ) ≤ stT297 48 := by
  have hc : ((947939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10945851633/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((947939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c49 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((986501/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102811/2500000) (δ := 749/50000000) (ψ := -19999/50000) 297 184
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t49 : ((1409143862971/10000000000000 : ℚ) : ℝ) ≤ stT297 49 := by
  have hc : ((986401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1409143862971/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((986401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c50 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((31031/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14807/500000) (δ := 14873/1000000000) (ψ := -19999/50000) 297 185
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t50 : ((351040193499/2500000000000 : ℚ) : ℝ) ≤ stT297 50 := by
  have hc : ((248223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351040193499/2500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((248223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c51 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((173537/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1300673/10000000) (δ := 7483/500000000) (ψ := -19999/50000) 297 186
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t51 : ((6074309619/50000000000 : ℚ) : ℝ) ≤ stT297 51 := by
  have hc : ((173517/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6074309619/50000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((173517/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c52 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((254713/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2590697/10000000) (δ := 14959/1000000000) (ψ := -19999/50000) 297 187
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t52 : ((1412615661/20000000000 : ℚ) : ℝ) ≤ stT297 52 := by
  have hc : ((254663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1412615661/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((254663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c53 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-3649/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4155371/10000000) (δ := 15051/1000000000) (ψ := -19999/50000) 297 188
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t53 : ((-2508891359/200000000000 : ℚ) : ℝ) ≤ stT297 53 := by
  have hc : ((-3653/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2508891359/200000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-3653/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c54 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-366589/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5984451/10000000) (δ := 3009/200000000) (ψ := -19999/50000) 297 189
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t54 : ((-124733154273/1250000000000 : ℚ) : ℝ) ≤ stT297 54 := by
  have hc : ((-366639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124733154273/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-366639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c55 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-996331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909939/2500000) (δ := 2989/200000000) (ψ := -19999/50000) 297 189
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t55 : ((-3358968901/25000000000 : ℚ) : ℝ) ≤ stT297 55 := by
  have hc : ((-996431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3358968901/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-996431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c56 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-131399/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5310529/10000000) (δ := 14937/1000000000) (ψ := -19999/50000) 297 190
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t56 : ((-5488212849/78125000000 : ℚ) : ℝ) ≤ stT297 56 := by
  have hc : ((-8214/15625 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5488212849/78125000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-8214/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c57 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((455549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2744519/10000000) (δ := 14873/1000000000) (ψ := -19999/50000) 297 191
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t57 : ((150814193717/2500000000000 : ℚ) : ℝ) ≤ stT297 57 := by
  have hc : ((455449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150814193717/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((455449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c58 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((4999/5000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50033/10000000) (δ := 14923/1000000000) (ψ := -19999/50000) 297 192
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t58 : ((1640837601/12500000000 : ℚ) : ℝ) ≤ stT297 58 := by
  have hc : ((9997/10000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1640837601/12500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((9997/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c59 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((337853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766351/2500000) (δ := 14887/1000000000) (ψ := -19999/50000) 297 193
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t59 : ((439716915417/10000000000000 : ℚ) : ℝ) ≤ stT297 59 := by
  have hc : ((337753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439716915417/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((337753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c60 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-32463/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -393381/625000) (δ := 15009/1000000000) (ψ := -19999/50000) 297 194
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t60 : ((-8382946933/80000000000 : ℚ) : ℝ) ≤ stT297 60 := by
  have hc : ((-32467/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8382946933/80000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-32467/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c61 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-731669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 597891/1000000) (δ := 7497/500000000) (ψ := -19999/50000) 297 194
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t61 : ((-936934342761/10000000000000 : ℚ) : ℝ) ≤ stT297 61 := by
  have hc : ((-731769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-936934342761/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-731769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c62 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((295803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146523/625000) (δ := 7501/500000000) (ψ := -19999/50000) 297 195
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t62 : ((375606605753/5000000000000 : ℚ) : ℝ) ≤ stT297 62 := by
  have hc : ((295753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375606605753/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((295753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c63 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((829089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483299/10000000) (δ := 7497/500000000) (ψ := -19999/50000) 297 196
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t63 : ((1044427490309/10000000000000 : ℚ) : ℝ) ≤ stT297 63 := by
  have hc : ((828989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1044427490309/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((828989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c64 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-293951/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5498149/10000000) (δ := 3729/250000000) (ψ := -19999/50000) 297 197
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t64 : ((-367501544001/5000000000000 : ℚ) : ℝ) ≤ stT297 64 := by
  have hc : ((-294001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367501544001/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-294001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c65 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-741089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6013719/10000000) (δ := 14987/1000000000) (ψ := -19999/50000) 297 197
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t65 : ((-229833073443/2500000000000 : ℚ) : ℝ) ≤ stT297 65 := by
  have hc : ((-741189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229833073443/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-741189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c66 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((791981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2627/16000) (δ := 14923/1000000000) (ψ := -19999/50000) 297 198
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t66 : ((487368704617/5000000000000 : ℚ) : ℝ) ≤ stT297 66 := by
  have hc : ((791881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487368704617/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((791881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c67 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((15967/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90639/312500) (δ := 14973/1000000000) (ψ := -19999/50000) 297 199
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t67 : ((9750950661/200000000000 : ℚ) : ℝ) ≤ stT297 67 := by
  have hc : ((15963/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9750950661/200000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((15963/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c68 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-995171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7608199/10000000) (δ := 14937/1000000000) (ψ := -19999/50000) 297 200
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t68 : ((-1206944241009/10000000000000 : ℚ) : ℝ) ≤ stT297 68 := by
  have hc : ((-995271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1206944241009/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-995271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c69 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((8583/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323141/1000000) (δ := 14937/1000000000) (ψ := -19999/50000) 297 200
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t69 : ((41315804631/1250000000000 : ℚ) : ℝ) ≤ stT297 69 := by
  have hc : ((68639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41315804631/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((68639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c70 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((11776/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112059/625000) (δ := 7479/500000000) (ψ := -19999/50000) 297 201
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t70 : ((56292549537/625000000000 : ℚ) : ℝ) ≤ stT297 70 := by
  have hc : ((188391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56292549537/625000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((188391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c71 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-468987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3484421/5000000) (δ := 15051/1000000000) (ψ := -19999/50000) 297 202
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t71 : ((-278322334467/2500000000000 : ℚ) : ℝ) ≤ stT297 71 := by
  have hc : ((-469037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278322334467/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-469037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c72 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((101491/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1707993/5000000) (δ := 14951/1000000000) (ψ := -19999/50000) 297 202
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t72 : ((119549334351/5000000000000 : ℚ) : ℝ) ≤ stT297 72 := by
  have hc : ((101441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119549334351/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((101441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c73 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((682089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -512613/2500000) (δ := 467/31250000) (ψ := -19999/50000) 297 203
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t73 : ((798207427479/10000000000000 : ℚ) : ℝ) ≤ stT297 73 := by
  have hc : ((681989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((798207427479/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((681989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c74 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-498437/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7656257/10000000) (δ := 7433/500000000) (ψ := -19999/50000) 297 204
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t74 : ((-579479672299/5000000000000 : ℚ) : ℝ) ≤ stT297 74 := by
  have hc : ((-498487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-579479672299/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-498487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c75 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((602507/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462079/2000000) (δ := 7483/500000000) (ψ := -19999/50000) 297 204
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t75 : ((6955993629/100000000000 : ℚ) : ℝ) ≤ stT297 75 := by
  have hc : ((602407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6955993629/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((602407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c76 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((145079/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27836/78125) (δ := 1503/100000000) (ψ := -19999/50000) 297 205
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t76 : ((83151110681/5000000000000 : ℚ) : ℝ) ≤ stT297 76 := by
  have hc : ((144979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83151110681/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((144979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c77 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-77481/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6143027/10000000) (δ := 14973/1000000000) (ψ := -19999/50000) 297 205
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t77 : ((-44154604273/500000000000 : ℚ) : ℝ) ≤ stT297 77 := by
  have hc : ((-77491/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44154604273/500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-77491/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c78 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((49999/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7919/5000000) (δ := 93/6250000) (ψ := -19999/50000) 297 206
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t78 : ((28303528169/250000000000 : ℚ) : ℝ) ≤ stT297 78 := by
  have hc : ((24997/25000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28303528169/250000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((24997/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c79 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-199289/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3116709/5000000) (δ := 2983/200000000) (ψ := -19999/50000) 297 207
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t79 : ((-3503840463/39062500000 : ℚ) : ℝ) ≤ stT297 79 := by
  have hc : ((-99657/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3503840463/39062500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-99657/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c80 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((80599/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3106341/10000000) (δ := 2983/200000000) (ψ := -19999/50000) 297 207
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t80 : ((45042195471/1250000000000 : ℚ) : ℝ) ≤ stT297 80 := by
  have hc : ((40287/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45042195471/1250000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((40287/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c81 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((54467/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -844479/2500000) (δ := 3727/250000000) (ψ := -19999/50000) 297 208
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t81 : ((30245552531/1250000000000 : ℚ) : ℝ) ≤ stT297 81 := by
  have hc : ((27221/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30245552531/1250000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((27221/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c82 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-16527/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5732633/10000000) (δ := 469/31250000) (ψ := -19999/50000) 297 208
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t82 : ((-9126895661/125000000000 : ℚ) : ℝ) ≤ stT297 82 := by
  have hc : ((-33059/50000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9126895661/125000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-33059/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c83 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((11561/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97519/1000000) (δ := 7501/500000000) (ψ := -19999/50000) 297 209
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t83 : ((25376934219/250000000000 : ℚ) : ℝ) ≤ stT297 83 := by
  have hc : ((46239/50000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25376934219/250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((46239/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c84 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-999681/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3895431/5000000) (δ := 29809/1000000000) (ψ := -19999/50000) 297 210
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t84 : ((-109085105129/1000000000000 : ℚ) : ℝ) ≤ stT297 84 := by
  have hc : ((-999781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109085105129/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-999781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c85 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((921649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 996217/10000000) (δ := 14909/1000000000) (ψ := -19999/50000) 297 210
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t85 : ((249889991487/2500000000000 : ℚ) : ℝ) ≤ stT297 85 := by
  have hc : ((921549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249889991487/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((921549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c86 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-74477/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3013733/5000000) (δ := 1877/125000000) (ψ := -19999/50000) 297 211
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t86 : ((-10040177217/125000000000 : ℚ) : ℝ) ≤ stT297 86 := by
  have hc : ((-74487/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10040177217/125000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-74487/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c87 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((130287/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1278251/5000000) (δ := 3729/250000000) (ψ := -19999/50000) 297 211
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t87 : ((4364232917/78125000000 : ℚ) : ℝ) ≤ stT297 87 := by
  have hc : ((65131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4364232917/78125000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((65131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c88 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-18199/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1166413/2500000) (δ := 14979/1000000000) (ψ := -19999/50000) 297 212
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t88 : ((-19406869321/625000000000 : ℚ) : ℝ) ≤ stT297 88 := by
  have hc : ((-72821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19406869321/625000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-72821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c89 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((81017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3724227/10000000) (δ := 14879/1000000000) (ψ := -19999/50000) 297 212
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t89 : ((85771777249/10000000000000 : ℚ) : ℝ) ≤ stT297 89 := by
  have hc : ((80917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85771777249/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((80917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c90 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((47813/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3687561/10000000) (δ := 1859/125000000) (ψ := -19999/50000) 297 213
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t90 : ((12586649049/1250000000000 : ℚ) : ℝ) ≤ stT297 90 := by
  have hc : ((47763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12586649049/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((47763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c91 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-233801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4516953/10000000) (δ := 29831/1000000000) (ψ := -19999/50000) 297 213
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t91 : ((-49038981957/2000000000000 : ℚ) : ℝ) ≤ stT297 91 := by
  have hc : ((-233901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49038981957/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-233901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c92 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((333789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3076191/10000000) (δ := 2973/200000000) (ψ := -19999/50000) 297 214
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t92 : ((86973702027/2500000000000 : ℚ) : ℝ) ≤ stT297 92 := by
  have hc : ((333689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86973702027/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((333689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c93 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-39821/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2475451/5000000) (δ := 2993/200000000) (ψ := -19999/50000) 297 214
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t93 : ((-5162854389/125000000000 : ℚ) : ℝ) ≤ stT297 93 := by
  have hc : ((-39831/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5162854389/125000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-39831/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c94 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((85997/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2815801/10000000) (δ := 7479/500000000) (ψ := -19999/50000) 297 215
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t94 : ((88678483317/2000000000000 : ℚ) : ℝ) ≤ stT297 94 := by
  have hc : ((85977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88678483317/2000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((85977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c95 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-8623/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5041409/10000000) (δ := 3009/200000000) (ψ := -19999/50000) 297 215
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t95 : ((-70792551/1600000000 : ℚ) : ℝ) ≤ stT297 95 := by
  have hc : ((-69/160 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70792551/1600000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-69/160 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c96 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((100603/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578323/2000000) (δ := 15051/1000000000) (ψ := -19999/50000) 297 216
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t96 : ((2566297959/62500000000 : ℚ) : ℝ) ≤ stT297 96 := by
  have hc : ((50289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2566297959/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((50289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c97 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-85797/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1200691/2500000) (δ := 15051/1000000000) (ψ := -19999/50000) 297 216
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t97 : ((-43569555117/1250000000000 : ℚ) : ℝ) ≤ stT297 97 := by
  have hc : ((-42911/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43569555117/1250000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-42911/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c98 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((126073/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -822437/2500000) (δ := 3761/250000000) (ψ := -19999/50000) 297 217
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t98 : ((15912798187/625000000000 : ℚ) : ℝ) ≤ stT297 98 := by
  have hc : ((126023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15912798187/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((126023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c99 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-128213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4248409/10000000) (δ := 3761/250000000) (ψ := -19999/50000) 297 217
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t99 : ((-64479720447/5000000000000 : ℚ) : ℝ) ≤ stT297 99 := by
  have hc : ((-128313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64479720447/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-128313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c100 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-14041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1998603/5000000) (δ := 14867/1000000000) (ψ := -19999/50000) 297 218
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t100 : ((-14091/5000000 : ℚ) : ℝ) ≤ stT297 100 := by
  have hc : ((-14091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14091/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-14091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c101 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((212771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1695483/5000000) (δ := 14867/1000000000) (ψ := -19999/50000) 297 218
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t101 : ((211615513827/10000000000000 : ℚ) : ℝ) ≤ stT297 101 := by
  have hc : ((212671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211615513827/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((212671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c102 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-26047/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1000333/2000000) (δ := 15029/1000000000) (ψ := -19999/50000) 297 219
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t102 : ((-25796573381/625000000000 : ℚ) : ℝ) ≤ stT297 102 := by
  have hc : ((-104213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25796573381/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-104213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c103 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((312019/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7007/31250) (δ := 7487/500000000) (ψ := -19999/50000) 297 219
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t103 : ((307392102801/5000000000000 : ℚ) : ℝ) ≤ stT297 103 := by
  have hc : ((311969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307392102801/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((311969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c104 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-811029/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6291763/10000000) (δ := 7461/500000000) (ψ := -19999/50000) 297 220
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t104 : ((-795377685949/10000000000000 : ℚ) : ℝ) ≤ stT297 104 := by
  have hc : ((-811129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-795377685949/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-811129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c105 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((947511/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813591/10000000) (δ := 14881/1000000000) (ψ := -19999/50000) 297 220
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t105 : ((9245783949/100000000000 : ℚ) : ℝ) ≤ stT297 105 := by
  have hc : ((947411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9245783949/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((947411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c106 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3925763/5000000) (δ := 14981/1000000000) (ψ := -19999/50000) 297 220
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t106 : ((-4856915643/50000000000 : ℚ) : ℝ) ≤ stT297 106 := by
  have hc : ((-10001/10000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4856915643/50000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-10001/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c107 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((938061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -884511/10000000) (δ := 1861/125000000) (ψ := -19999/50000) 297 221
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t107 : ((56672541581/625000000000 : ℚ) : ℝ) ≤ stT297 107 := by
  have hc : ((937961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56672541581/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((937961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c108 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-743449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6022521/10000000) (δ := 1861/125000000) (ψ := -19999/50000) 297 221
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t108 : ((-715480768799/10000000000000 : ℚ) : ℝ) ≤ stT297 108 := by
  have hc : ((-743549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-715480768799/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-743549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c109 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((210229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2842117/10000000) (δ := 3727/250000000) (ψ := -19999/50000) 297 222
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t109 : ((100657455427/2500000000000 : ℚ) : ℝ) ≤ stT297 109 := by
  have hc : ((210179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100657455427/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((210179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c110 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-4709/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 984691/2500000) (δ := 469/31250000) (ψ := -19999/50000) 297 222
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t110 : ((-4585203567/10000000000000 : ℚ) : ℝ) ≤ stT297 110 := by
  have hc : ((-4809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4585203567/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-4809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c111 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-217061/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -315603/625000) (δ := 14903/1000000000) (ψ := -19999/50000) 297 223
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t111 : ((-103036321269/2500000000000 : ℚ) : ℝ) ≤ stT297 111 := by
  have hc : ((-217111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103036321269/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-217111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c112 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((199953/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1609537/10000000) (δ := 3/200000) (ψ := -19999/50000) 297 223
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t112 : ((23614270801/312500000000 : ℚ) : ℝ) ≤ stT297 112 := by
  have hc : ((24991/31250 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23614270801/312500000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((24991/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c113 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-989899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7498343/10000000) (δ := 1501/100000000) (ψ := -19999/50000) 297 224
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t113 : ((-931312849279/10000000000000 : ℚ) : ℝ) ≤ stT297 113 := by
  have hc : ((-989999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-931312849279/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-989999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c114 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((927701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -956473/10000000) (δ := 14893/1000000000) (ψ := -19999/50000) 297 224
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t114 : ((173755436517/2000000000000 : ℚ) : ℝ) ≤ stT297 114 := by
  have hc : ((927601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173755436517/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((927601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c115 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-119523/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5528299/10000000) (δ := 14993/1000000000) (ψ := -19999/50000) 297 224
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t115 : ((-22294889043/400000000000 : ℚ) : ℝ) ≤ stT297 115 := by
  have hc : ((-119543/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22294889043/400000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-119543/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c116 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((70299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3751099/10000000) (δ := 7443/500000000) (ψ := -19999/50000) 297 225
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t116 : ((16294521681/2500000000000 : ℚ) : ℝ) ≤ stT297 116 := by
  have hc : ((70199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16294521681/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((70199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c117 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((249241/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2622373/10000000) (δ := 15017/1000000000) (ψ := -19999/50000) 297 225
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t117 : ((460754159/10000000000 : ℚ) : ℝ) ≤ stT297 117 := by
  have hc : ((249191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((460754159/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((249191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c118 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-113357/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1691599/2500000) (δ := 14879/1000000000) (ψ := -19999/50000) 297 226
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t118 : ((-8349210197/100000000000 : ℚ) : ℝ) ≤ stT297 118 := by
  have hc : ((-226739/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8349210197/100000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-226739/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c119 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((49001/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -500587/10000000) (δ := 14879/1000000000) (ψ := -19999/50000) 297 226
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t119 : ((5614316901/62500000000 : ℚ) : ℝ) ≤ stT297 119 := by
  have hc : ((12249/12500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5614316901/62500000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((12249/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c120 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-65513/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1428219/2500000) (δ := 3731/250000000) (ψ := -19999/50000) 297 226
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t120 : ((-59814046533/1000000000000 : ℚ) : ℝ) ≤ stT297 120 := by
  have hc : ((-65523/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59814046533/1000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-65523/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c121 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((4687/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -958307/2500000) (δ := 15031/1000000000) (ψ := -19999/50000) 297 227
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t121 : ((849908241/250000000000 : ℚ) : ℝ) ≤ stT297 121 := by
  have hc : ((9349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((849908241/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((9349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c122 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((76603/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1138959/5000000) (δ := 14931/1000000000) (ψ := -19999/50000) 297 227
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t122 : ((138683490617/2500000000000 : ℚ) : ℝ) ≤ stT297 122 := by
  have hc : ((153181/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138683490617/2500000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((153181/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c123 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-981227/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1473759/2000000) (δ := 7469/500000000) (ψ := -19999/50000) 297 228
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t123 : ((-88483311609/1000000000000 : ℚ) : ℝ) ≤ stT297 123 := by
  have hc : ((-981327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88483311609/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-981327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c124 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((856343/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84789/625000) (δ := 7469/500000000) (ψ := -19999/50000) 297 228
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t124 : ((384464238159/5000000000000 : ℚ) : ℝ) ≤ stT297 124 := by
  have hc : ((856243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384464238159/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((856243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c125 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-268771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1151821/2500000) (δ := 2993/200000000) (ψ := -19999/50000) 297 228
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t125 : ((-60121437697/2500000000000 : ℚ) : ℝ) ≤ stT297 125 := by
  have hc : ((-268871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60121437697/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-268871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c126 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-240993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -518429/1000000) (δ := 7523/500000000) (ψ := -19999/50000) 297 229
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t126 : ((-214738218453/5000000000000 : ℚ) : ℝ) ≤ stT297 126 := by
  have hc : ((-241043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214738218453/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-241043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c127 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((96267/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 342623/5000000) (δ := 14957/1000000000) (ψ := -19999/50000) 297 229
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t127 : ((21353556623/250000000000 : ℚ) : ℝ) ≤ stT297 127 := by
  have hc : ((96257/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21353556623/250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((96257/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c128 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-858703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3254411/5000000) (δ := 14957/1000000000) (ψ := -19999/50000) 297 229
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t128 : ((-189770557713/2500000000000 : ℚ) : ℝ) ≤ stT297 128 := by
  have hc : ((-858803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189770557713/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-858803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c129 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((201073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1710429/5000000) (δ := 301/20000000) (ψ := -19999/50000) 297 230
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t129 : ((3538933557/200000000000 : ℚ) : ℝ) ≤ stT297 129 := by
  have hc : ((200973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3538933557/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((200973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c130 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((300881/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2312727/10000000) (δ := 301/20000000) (ψ := -19999/50000) 297 230
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t130 : ((131923117599/2500000000000 : ℚ) : ℝ) ≤ stT297 130 := by
  have hc : ((300831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131923117599/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((300831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c131 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-499119/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7705533/10000000) (δ := 15043/1000000000) (ψ := -19999/50000) 297 231
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t131 : ((-87225290229/1000000000000 : ℚ) : ℝ) ≤ stT297 131 := by
  have hc : ((-499169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87225290229/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-499169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c132 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((13591/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2059117/10000000) (δ := 743/50000000) (ψ := -19999/50000) 297 231
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t132 : ((2956925633/50000000000 : ℚ) : ℝ) ≤ stT297 132 := by
  have hc : ((13589/20000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2956925633/50000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((13589/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c133 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((152329/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3544679/10000000) (δ := 743/50000000) (ψ := -19999/50000) 297 231
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t133 : ((131999135961/10000000000000 : ℚ) : ℝ) ≤ stT297 133 := by
  have hc : ((152229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131999135961/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((152229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c134 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-438551/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6601477/10000000) (δ := 7459/250000000) (ψ := -19999/50000) 297 232
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t134 : ((-378893807269/5000000000000 : ℚ) : ℝ) ≤ stT297 134 := by
  have hc : ((-438601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378893807269/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-438601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c135 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((453979/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -540513/5000000) (δ := 14967/1000000000) (ψ := -19999/50000) 297 232
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t135 : ((195339720499/2500000000000 : ℚ) : ℝ) ≤ stT297 135 := by
  have hc : ((453929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195339720499/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((453929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c136 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-37513/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2199349/5000000) (δ := 14867/1000000000) (ψ := -19999/50000) 297 232
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t136 : ((-32184284769/2000000000000 : ℚ) : ℝ) ≤ stT297 136 := by
  have hc : ((-37533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32184284769/2000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-37533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c137 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-140237/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1467409/2500000) (δ := 7437/500000000) (ψ := -19999/50000) 297 233
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t137 : ((-59914845003/1000000000000 : ℚ) : ℝ) ≤ stT297 137 := by
  have hc : ((-140257/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59914845003/1000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-140257/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c138 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((491203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58707/1250000) (δ := 7487/500000000) (ψ := -19999/50000) 297 233
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t138 : ((52262117271/625000000000 : ℚ) : ℝ) ≤ stT297 138 := by
  have hc : ((491153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52262117271/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((491153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c139 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-376273/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 611427/1250000) (δ := 15029/1000000000) (ψ := -19999/50000) 297 233
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t139 : ((-319235438497/10000000000000 : ℚ) : ℝ) ≤ stT297 139 := by
  have hc : ((-376373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319235438497/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-376373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c140 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-293269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343371/625000) (δ := 15021/1000000000) (ψ := -19999/50000) 297 234
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t140 : ((-49580003889/1000000000000 : ℚ) : ℝ) ≤ stT297 140 := by
  have hc : ((-293319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49580003889/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-293319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c141 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((996499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104633/5000000) (δ := 7441/500000000) (ψ := -19999/50000) 297 234
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t141 : ((839118414249/10000000000000 : ℚ) : ℝ) ≤ stT297 141 := by
  have hc : ((996399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((839118414249/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((996399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c142 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-429967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 503813/1000000) (δ := 7441/500000000) (ψ := -19999/50000) 297 234
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t142 : ((-180452242597/5000000000000 : ℚ) : ℝ) ≤ stT297 142 := by
  have hc : ((-430067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180452242597/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-430067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c143 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-2301/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1091853/2000000) (δ := 14989/1000000000) (ψ := -19999/50000) 297 235
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t143 : ((-9622648201/200000000000 : ℚ) : ℝ) ≤ stT297 143 := by
  have hc : ((-11507/20000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9622648201/200000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-11507/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c144 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((198701/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7127/250000) (δ := 7457/500000000) (ψ := -19999/50000) 297 235
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t144 : ((165567433773/2000000000000 : ℚ) : ℝ) ≤ stT297 144 := by
  have hc : ((198681/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165567433773/2000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((198681/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c145 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-181069/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4853391/10000000) (δ := 7507/500000000) (ψ := -19999/50000) 297 235
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t145 : ((-30082235829/1000000000000 : ℚ) : ℝ) ≤ stT297 145 := by
  have hc : ((-181119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30082235829/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-181119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c146 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-666707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1437861/2500000) (δ := 15007/1000000000) (ψ := -19999/50000) 297 236
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t146 : ((-275926737021/5000000000000 : ℚ) : ℝ) ≤ stT297 146 := by
  have hc : ((-666807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275926737021/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-666807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c147 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((962889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -683213/10000000) (δ := 14907/1000000000) (ψ := -19999/50000) 297 236
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t147 : ((397047444077/5000000000000 : ℚ) : ℝ) ≤ stT297 147 := by
  have hc : ((962789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((397047444077/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((962789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c148 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-168679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2175357/5000000) (δ := 15007/1000000000) (ψ := -19999/50000) 297 236
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t148 : ((-27747098821/2000000000000 : ℚ) : ℝ) ≤ stT297 148 := by
  have hc : ((-168779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27747098821/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-168779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c149 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-826057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317859/500000) (δ := 3/200000) (ψ := -19999/50000) 297 237
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t149 : ((-21150445357/312500000000 : ℚ) : ℝ) ≤ stT297 149 := by
  have hc : ((-826157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21150445357/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-826157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c150 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((849231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1390671/10000000) (δ := 15003/1000000000) (ψ := -19999/50000) 297 237
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t150 : ((43332004061/625000000000 : ℚ) : ℝ) ≤ stT297 150 := by
  have hc : ((849131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43332004061/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((849131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c151 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((30603/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110717/312500) (δ := 149/10000000) (ψ := -19999/50000) 297 237
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t151 : ((6222019601/500000000000 : ℚ) : ℝ) ≤ stT297 151 := by
  have hc : ((30583/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6222019601/500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((30583/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c152 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-972283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7263999/10000000) (δ := 1501/100000000) (ψ := -19999/50000) 297 238
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t152 : ((-197176907591/2500000000000 : ℚ) : ℝ) ≤ stT297 152 := by
  have hc : ((-972383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197176907591/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-972383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c153 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((115023/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239513/1000000) (δ := 14893/1000000000) (ψ := -19999/50000) 297 238
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t153 : ((23243601339/500000000000 : ℚ) : ℝ) ≤ stT297 153 := by
  have hc : ((115003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23243601339/500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((115003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c154 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((279833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 488407/2000000) (δ := 1491/100000000) (ψ := -19999/50000) 297 238
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t154 : ((112727648313/2500000000000 : ℚ) : ℝ) ≤ stT297 154 := by
  have hc : ((279783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112727648313/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((279783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c155 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-485377/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3623933/5000000) (δ := 14893/1000000000) (ψ := -19999/50000) 297 238
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t155 : ((-19495233747/250000000000 : ℚ) : ℝ) ≤ stT297 155 := by
  have hc : ((-485427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19495233747/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-485427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c156 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((12073/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1842577/5000000) (δ := 7443/500000000) (ψ := -19999/50000) 297 239
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t156 : ((30175371/3906250000 : ℚ) : ℝ) ≤ stT297 156 := by
  have hc : ((24121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30175371/3906250000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((24121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c157 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((91157/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1059273/10000000) (δ := 15017/1000000000) (ψ := -19999/50000) 297 239
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t157 : ((36371572321/500000000000 : ℚ) : ℝ) ≤ stT297 157 := by
  have hc : ((91147/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36371572321/500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((91147/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c158 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-84159/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2886777/5000000) (δ := 15017/1000000000) (ψ := -19999/50000) 297 239
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t158 : ((-66963310197/1250000000000 : ℚ) : ℝ) ≤ stT297 158 := by
  have hc : ((-168343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66963310197/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-168343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c159 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-504787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5249829/10000000) (δ := 7489/500000000) (ψ := -19999/50000) 297 240
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t159 : ((-100100411281/2500000000000 : ℚ) : ℝ) ≤ stT297 159 := by
  have hc : ((-504887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100100411281/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-504887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c160 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((242961/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594651/10000000) (δ := 7489/500000000) (ψ := -19999/50000) 297 240
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t160 : ((24007208823/312500000000 : ℚ) : ℝ) ≤ stT297 160 := by
  have hc : ((30367/31250 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24007208823/312500000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((30367/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c161 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-4179/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 503937/1250000) (δ := 601/40000000) (ψ := -19999/50000) 297 240
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t161 : ((-3301396979/1000000000000 : ℚ) : ℝ) ≤ stT297 161 := by
  have hc : ((-4189/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3301396979/1000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-4189/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c162 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-38093/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1769727/2500000) (δ := 14971/1000000000) (ψ := -19999/50000) 297 241
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t162 : ((-1197274419/16000000000 : ℚ) : ℝ) ≤ stT297 162 := by
  have hc : ((-38097/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1197274419/16000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-38097/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c163 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((107411/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2509637/10000000) (δ := 14871/1000000000) (ψ := -19999/50000) 297 241
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t163 : ((4205753733/100000000000 : ℚ) : ℝ) ≤ stT297 163 := by
  have hc : ((107391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4205753733/100000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((107391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c164 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((171893/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1015821/5000000) (δ := 1879/125000000) (ψ := -19999/50000) 297 241
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t164 : ((8387888839/156250000000 : ℚ) : ℝ) ≤ stT297 164 := by
  have hc : ((42967/62500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8387888839/156250000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((42967/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c165 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-108261/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6545299/10000000) (δ := 14871/1000000000) (ψ := -19999/50000) 297 241
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t165 : ((-168581622953/2500000000000 : ℚ) : ℝ) ≤ stT297 165 := by
  have hc : ((-216547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168581622953/2500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-216547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c166 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-295239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146133/312500) (δ := 15039/1000000000) (ψ := -19999/50000) 297 242
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t166 : ((-229227660189/10000000000000 : ℚ) : ℝ) ≤ stT297 166 := by
  have hc : ((-295339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229227660189/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-295339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c167 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((199249/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216727/10000000) (δ := 14939/1000000000) (ψ := -19999/50000) 297 242
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t167 : ((154167982467/2000000000000 : ℚ) : ℝ) ≤ stT297 167 := by
  have hc : ((199229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154167982467/2000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((199229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c168 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-923/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527009/1250000) (δ := 929/62500000) (ψ := -19999/50000) 297 242
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t168 : ((-3563637023/400000000000 : ℚ) : ℝ) ≤ stT297 168 := by
  have hc : ((-4619/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3563637023/400000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-4619/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c169 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-476551/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3542651/5000000) (δ := 7473/500000000) (ψ := -19999/50000) 297 243
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t169 : ((-366616263831/5000000000000 : ℚ) : ℝ) ≤ stT297 169 := by
  have hc : ((-476601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366616263831/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-476601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c170 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((469643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108191/400000) (δ := 14857/1000000000) (ψ := -19999/50000) 297 243
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t170 : ((90030644363/2500000000000 : ℚ) : ℝ) ≤ stT297 170 := by
  have hc : ((469543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90030644363/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((469543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c171 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((789977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 825031/5000000) (δ := 7473/500000000) (ψ := -19999/50000) 297 243
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t171 : ((604033949563/10000000000000 : ℚ) : ℝ) ≤ stT297 171 := by
  have hc : ((789877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((604033949563/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((789877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c172 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-91479/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195901/2000000) (δ := 14857/1000000000) (ψ := -19999/50000) 297 243
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t172 : ((-139523256619/2500000000000 : ℚ) : ℝ) ≤ stT297 172 := by
  have hc : ((-182983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139523256619/2500000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-182983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c173 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-140923/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339007/625000) (δ := 301/20000000) (ψ := -19999/50000) 297 244
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t173 : ((-13395098891/312500000000 : ℚ) : ℝ) ≤ stT297 173 := by
  have hc : ((-35237/62500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13395098891/312500000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-35237/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c174 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((112127/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -286141/2500000) (δ := 14953/1000000000) (ψ := -19999/50000) 297 244
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t174 : ((84993778221/1250000000000 : ℚ) : ℝ) ≤ stT297 174 := by
  have hc : ((224229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84993778221/1250000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((224229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c175 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((320829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38881/125000) (δ := 301/20000000) (ψ := -19999/50000) 297 244
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t175 : ((30306003939/1250000000000 : ℚ) : ℝ) ≤ stT297 175 := by
  have hc : ((320729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30306003939/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((320729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c176 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-489521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1468249/2000000) (δ := 301/20000000) (ψ := -19999/50000) 297 244
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t176 : ((-369028338809/5000000000000 : ℚ) : ℝ) ≤ stT297 176 := by
  have hc : ((-489571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369028338809/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-489571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c177 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-93013/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4159861/10000000) (δ := 187/12500000) (ψ := -19999/50000) 297 245
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t177 : ((-69988107111/10000000000000 : ℚ) : ℝ) ≤ stT297 177 := by
  have hc : ((-93113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69988107111/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-93113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c178 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((999957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4647/2000000) (δ := 14943/1000000000) (ψ := -19999/50000) 297 245
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t178 : ((749423817067/10000000000000 : ℚ) : ℝ) ≤ stT297 178 := by
  have hc : ((999857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((749423817067/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((999857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c179 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-51101/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4182943/10000000) (δ := 743/50000000) (ψ := -19999/50000) 297 245
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t179 : ((-9558024709/1250000000000 : ℚ) : ℝ) ≤ stT297 179 := by
  have hc : ((-51151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9558024709/1250000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-51151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c180 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-3071/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7388553/10000000) (δ := 2987/200000000) (ψ := -19999/50000) 297 246
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t180 : ((-9156884799/125000000000 : ℚ) : ℝ) ≤ stT297 180 := by
  have hc : ((-49141/50000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9156884799/125000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-49141/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c181 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((64467/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1637477/5000000) (δ := 1871/125000000) (ψ := -19999/50000) 297 246
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t181 : ((11974837987/625000000000 : ℚ) : ℝ) ≤ stT297 181 := by
  have hc : ((32221/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11974837987/625000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((32221/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c182 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((947213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 203981/2500000) (δ := 1871/125000000) (ψ := -19999/50000) 297 246
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t182 : ((702046564137/10000000000000 : ℚ) : ℝ) ≤ stT297 182 := by
  have hc : ((947113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((702046564137/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((947113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c183 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-37369/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1221113/2500000) (δ := 3007/200000000) (ψ := -19999/50000) 297 246
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t183 : ((-13815689569/500000000000 : ℚ) : ℝ) ≤ stT297 183 := by
  have hc : ((-37379/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13815689569/500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-37379/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c184 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-454333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6777183/10000000) (δ := 933/62500000) (ψ := -19999/50000) 297 247
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t184 : ((-33497569143/500000000000 : ℚ) : ℝ) ≤ stT297 184 := by
  have hc : ((-454383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33497569143/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-454383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c185 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((113153/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2752759/10000000) (δ := 3757/250000000) (ψ := -19999/50000) 297 247
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t185 : ((5198330587/156250000000 : ℚ) : ℝ) ≤ stT297 185 := by
  have hc : ((14141/31250 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5198330587/156250000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((14141/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c186 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((1097/1250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124991/1000000) (δ := 3757/250000000) (ψ := -19999/50000) 297 247
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t186 : ((51473097/800000000 : ℚ) : ℝ) ≤ stT297 186 := by
  have hc : ((351/400 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51473097/800000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((351/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c187 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-498339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1046239/2000000) (δ := 3757/250000000) (ψ := -19999/50000) 297 247
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t187 : ((-364494982847/10000000000000 : ℚ) : ℝ) ≤ stT297 187 := by
  have hc : ((-498439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364494982847/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-498439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c188 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-215083/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6516793/10000000) (δ := 15021/1000000000) (ψ := -19999/50000) 297 248
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t188 : ((-1568836421/25000000000 : ℚ) : ℝ) ≤ stT297 188 := by
  have hc : ((-53777/62500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1568836421/25000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-53777/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c189 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((513873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -644439/2500000) (δ := 14921/1000000000) (ψ := -19999/50000) 297 248
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t189 : ((11678574063/312500000000 : ℚ) : ℝ) ≤ stT297 189 := by
  have hc : ((513773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11678574063/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((513773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c190 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((859673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1340417/10000000) (δ := 7491/500000000) (ψ := -19999/50000) 297 248
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t190 : ((155899895437/2500000000000 : ℚ) : ℝ) ≤ stT297 190 := by
  have hc : ((859573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155899895437/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((859573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c191 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-50073/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327381/625000) (δ := 14921/1000000000) (ψ := -19999/50000) 297 248
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t191 : ((-1449552269/40000000000 : ℚ) : ℝ) ≤ stT297 191 := by
  have hc : ((-50083/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1449552269/40000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-50083/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c192 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-13678/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3296303/5000000) (δ := 14989/1000000000) (ψ := -19999/50000) 297 249
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t192 : ((-19744752203/312500000000 : ℚ) : ℝ) ≤ stT297 192 := by
  have hc : ((-218873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19744752203/312500000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-218873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c193 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((458769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2735467/10000000) (δ := 14989/1000000000) (ψ := -19999/50000) 297 249
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t193 : ((66031365247/2000000000000 : ℚ) : ℝ) ≤ stT297 193 := by
  have hc : ((458669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66031365247/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((458669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c194 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((904449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1101773/10000000) (δ := 14989/1000000000) (ψ := -19999/50000) 297 249
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t194 : ((324642299671/5000000000000 : ℚ) : ℝ) ≤ stT297 194 := by
  have hc : ((904349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324642299671/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((904349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c195 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-386569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2459631/5000000) (δ := 7457/500000000) (ψ := -19999/50000) 297 249
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t195 : ((-55379894187/2000000000000 : ℚ) : ℝ) ≤ stT297 195 := by
  have hc : ((-386669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55379894187/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-386669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c196 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-37639/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6990739/10000000) (δ := 3749/250000000) (ψ := -19999/50000) 297 250
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t196 : ((-13443933949/200000000000 : ℚ) : ℝ) ≤ stT297 196 := by
  have hc : ((-37643/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13443933949/200000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-37643/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c197 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((141041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3212083/10000000) (δ := 15007/1000000000) (ψ := -19999/50000) 297 250
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t197 : ((10045185777/500000000000 : ℚ) : ℝ) ≤ stT297 197 := by
  have hc : ((140991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10045185777/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((140991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c198 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((488061/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273709/5000000) (δ := 3749/250000000) (ψ := -19999/50000) 297 250
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t198 : ((346814289359/5000000000000 : ℚ) : ℝ) ≤ stT297 198 := by
  have hc : ((488011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346814289359/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((488011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c199 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-17987/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267999/625000) (δ := 14907/1000000000) (ψ := -19999/50000) 297 250
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t199 : ((-12759521559/1250000000000 : ℚ) : ℝ) ≤ stT297 199 := by
  have hc : ((-35999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12759521559/1250000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-35999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c200 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-998059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3849099/5000000) (δ := 14899/1000000000) (ψ := -19999/50000) 297 251
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t200 : ((-705805216013/10000000000000 : ℚ) : ℝ) ≤ stT297 200 := by
  have hc : ((-998159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-705805216013/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-998159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c201 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-13581/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -798981/2000000) (δ := 14899/1000000000) (ψ := -19999/50000) 297 251
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t201 : ((-4807285663/2500000000000 : ℚ) : ℝ) ≤ stT297 201 := by
  have hc : ((-13631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4807285663/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-13631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c202 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((992317/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3101/100000) (δ := 1863/125000000) (ψ := -19999/50000) 297 251
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t202 : ((698120904549/10000000000000 : ℚ) : ℝ) ≤ stT297 202 := by
  have hc : ((992217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((698120904549/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((992217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c203 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((226187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 839147/2500000) (δ := 3751/250000000) (ψ := -19999/50000) 297 251
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t203 : ((79340936997/5000000000000 : ℚ) : ℝ) ≤ stT297 203 := by
  have hc : ((226087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79340936997/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((226087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c204 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-942921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7005233/10000000) (δ := 3751/250000000) (ψ := -19999/50000) 297 251
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t204 : ((-660247665961/10000000000000 : ℚ) : ℝ) ≤ stT297 204 := by
  have hc : ((-943021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660247665961/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-943021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c205 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-3537/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2535953/5000000) (δ := 937/62500000) (ψ := -19999/50000) 297 252
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t205 : ((-12354545959/400000000000 : ℚ) : ℝ) ≤ stT297 205 := by
  have hc : ((-17689/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12354545959/400000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-17689/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c206 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((834539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22793/156250) (δ := 14911/1000000000) (ψ := -19999/50000) 297 252
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t206 : ((581381187787/10000000000000 : ℚ) : ℝ) ≤ stT297 206 := by
  have hc : ((834439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581381187787/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((834439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c207 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((328203/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068439/5000000) (δ := 937/62500000) (ψ := -19999/50000) 297 252
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t207 : ((28510260793/625000000000 : ℚ) : ℝ) ≤ stT297 207 := by
  have hc : ((328153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28510260793/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((328153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c208 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-327917/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5715209/10000000) (δ := 15011/1000000000) (ψ := -19999/50000) 297 252
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t208 : ((-1776597239/39062500000 : ℚ) : ℝ) ≤ stT297 208 := by
  have hc : ((-327967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1776597239/39062500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-327967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c209 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-842461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -803947/1250000) (δ := 7459/500000000) (ψ := -19999/50000) 297 253
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t209 : ((-116562416423/2000000000000 : ℚ) : ℝ) ≤ stT297 209 := by
  have hc : ((-842561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116562416423/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-842561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c210 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((80791/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2887401/10000000) (δ := 2977/200000000) (ψ := -19999/50000) 297 253
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t210 : ((11147448023/400000000000 : ℚ) : ℝ) ≤ stT297 210 := by
  have hc : ((80771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11147448023/400000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((80771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c211 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((967419/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7999/125000) (δ := 7509/500000000) (ψ := -19999/50000) 297 253
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t211 : ((166482371133/2500000000000 : ℚ) : ℝ) ≤ stT297 211 := by
  have hc : ((967319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166482371133/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((967319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c212 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-44649/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2075267/5000000) (δ := 7459/500000000) (ψ := -19999/50000) 297 253
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t212 : ((-30699407297/5000000000000 : ℚ) : ℝ) ≤ stT297 212 := by
  have hc : ((-44699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30699407297/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-44699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c213 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-996497/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1528933/2000000) (δ := 7509/500000000) (ψ := -19999/50000) 297 253
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t213 : ((-682857301833/10000000000000 : ℚ) : ℝ) ≤ stT297 213 := by
  have hc : ((-996597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682857301833/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-996597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c214 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-260369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4585503/10000000) (δ := 7439/500000000) (ψ := -19999/50000) 297 254
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t214 : ((-89026480917/5000000000000 : ℚ) : ℝ) ≤ stT297 214 := by
  have hc : ((-260469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89026480917/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-260469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c215 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((900627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8781/78125) (δ := 7439/500000000) (ψ := -19999/50000) 297 254
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t215 : ((307077005419/5000000000000 : ℚ) : ℝ) ≤ stT297 215 := by
  have hc : ((900527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307077005419/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((900527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c216 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((299473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2321529/10000000) (δ := 7439/500000000) (ψ := -19999/50000) 297 254
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t216 : ((203731301699/5000000000000 : ℚ) : ℝ) ≤ stT297 216 := by
  have hc : ((299423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203731301699/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((299423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c217 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-666593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2875531/5000000) (δ := 7489/500000000) (ψ := -19999/50000) 297 254
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t217 : ((-90516241917/2000000000000 : ℚ) : ℝ) ≤ stT297 217 := by
  have hc : ((-666693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90516241917/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-666693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c218 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-17313/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6543109/10000000) (δ := 14971/1000000000) (ψ := -19999/50000) 297 255
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t218 : ((-1172720709/20000000000 : ℚ) : ℝ) ≤ stT297 218 := by
  have hc : ((-3463/4000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1172720709/20000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-3463/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c219 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((61551/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3144909/10000000) (δ := 14871/1000000000) (ψ := -19999/50000) 297 255
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t219 : ((41578773347/2000000000000 : ℚ) : ℝ) ≤ stT297 219 := by
  have hc : ((61531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41578773347/2000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((61531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c220 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((995481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237773/10000000) (δ := 1879/125000000) (ψ := -19999/50000) 297 255
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t220 : ((671084874819/10000000000000 : ℚ) : ℝ) ≤ stT297 220 := by
  have hc : ((995381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671084874819/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((995381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c221 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((128377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3605159/10000000) (δ := 1879/125000000) (ψ := -19999/50000) 297 255
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t221 : ((2696510817/312500000000 : ℚ) : ℝ) ≤ stT297 221 := by
  have hc : ((128277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2696510817/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((128277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c222 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-234089/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6957249/10000000) (δ := 14871/1000000000) (ψ := -19999/50000) 297 255
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t222 : ((-78563624949/1250000000000 : ℚ) : ℝ) ≤ stT297 222 := by
  have hc : ((-117057/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78563624949/1250000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-117057/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c223 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-560221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2706811/5000000) (δ := 14939/1000000000) (ψ := -19999/50000) 297 256
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t223 : ((-7504379153/200000000000 : ℚ) : ℝ) ≤ stT297 223 := by
  have hc : ((-560321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7504379153/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-560321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c224 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((167501/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1045727/5000000) (δ := 15039/1000000000) (ψ := -19999/50000) 297 256
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t224 : ((27974897957/625000000000 : ℚ) : ℝ) ≤ stT297 224 := by
  have hc : ((41869/62500 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27974897957/625000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((41869/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c225 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((884033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 607969/5000000) (δ := 15039/1000000000) (ψ := -19999/50000) 297 256
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t225 : ((294644038689/5000000000000 : ℚ) : ℝ) ≤ stT297 225 := by
  have hc : ((883933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294644038689/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((883933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c226 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-230547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4508591/10000000) (δ := 29739/1000000000) (ψ := -19999/50000) 297 256
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t226 : ((-153424308577/10000000000000 : ℚ) : ℝ) ≤ stT297 226 := by
  have hc : ((-230647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153424308577/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-230647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c227 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-999639/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3893383/5000000) (δ := 15039/1000000000) (ψ := -19999/50000) 297 256
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t227 : ((-165887692009/2500000000000 : ℚ) : ℝ) ≤ stT297 227 := by
  have hc : ((-999739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165887692009/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-999739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c228 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-5761/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -931493/2000000) (δ := 3739/250000000) (ψ := -19999/50000) 297 257
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t228 : ((-3816644721/200000000000 : ℚ) : ℝ) ≤ stT297 228 := by
  have hc : ((-5763/20000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3816644721/200000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-5763/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c229 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((422777/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -351997/2500000) (δ := 3739/250000000) (ψ := -19999/50000) 297 257
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t229 : ((139672805343/2500000000000 : ℚ) : ℝ) ≤ stT297 229 := by
  have hc : ((422727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139672805343/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((422727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c230 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((372279/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 456827/2500000) (δ := 15047/1000000000) (ψ := -19999/50000) 297 257
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t230 : ((12272017901/250000000000 : ℚ) : ℝ) ≤ stT297 230 := by
  have hc : ((372229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12272017901/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((372229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c231 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-433733/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504857/1000000) (δ := 15047/1000000000) (ψ := -19999/50000) 297 257
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t231 : ((-8920040313/312500000000 : ℚ) : ℝ) ≤ stT297 231 := by
  have hc : ((-433833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8920040313/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-433833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c232 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-987107/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7452091/10000000) (δ := 14949/1000000000) (ψ := -19999/50000) 297 258
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t232 : ((-648133973331/10000000000000 : ℚ) : ℝ) ≤ stT297 232 := by
  have hc : ((-987207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-648133973331/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-987207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c233 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-5289/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1064631/2500000) (δ := 7427/500000000) (ψ := -19999/50000) 297 258
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t233 : ((-1733780373/200000000000 : ℚ) : ℝ) ≤ stT297 233 := by
  have hc : ((-5293/40000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1733780373/200000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-5293/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c234 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((908361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1078619/10000000) (δ := 7477/500000000) (ψ := -19999/50000) 297 258
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t234 : ((14843709523/250000000000 : ℚ) : ℝ) ≤ stT297 234 := by
  have hc : ((908261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14843709523/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((908261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c235 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((671119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1043849/5000000) (δ := 7477/500000000) (ψ := -19999/50000) 297 258
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t235 : ((54715560279/1250000000000 : ℚ) : ℝ) ≤ stT297 235 := by
  have hc : ((671019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54715560279/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((671019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c236 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-125397/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 209623/400000) (δ := 15049/1000000000) (ψ := -19999/50000) 297 258
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t236 : ((-8164282379/250000000000 : ℚ) : ℝ) ≤ stT297 236 := by
  have hc : ((-62711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8164282379/250000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-62711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c237 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-977939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58623/80000) (δ := 14861/1000000000) (ψ := -19999/50000) 297 259
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t237 : ((-63530479323/1000000000000 : ℚ) : ℝ) ≤ stT297 237 := by
  have hc : ((-978039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63530479323/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-978039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c238 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-21923/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4201579/10000000) (δ := 7471/500000000) (ψ := -19999/50000) 297 259
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t238 : ((-3555885093/500000000000 : ℚ) : ℝ) ≤ stT297 238 := by
  have hc : ((-21943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3555885093/500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-21943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c239 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((906727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1088351/10000000) (δ := 7521/500000000) (ψ := -19999/50000) 297 259
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t239 : ((293224024221/5000000000000 : ℚ) : ℝ) ≤ stT297 239 := by
  have hc : ((906627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293224024221/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((906627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c240 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((693289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502971/2500000) (δ := 14861/1000000000) (ψ := -19999/50000) 297 259
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t240 : ((447451419933/10000000000000 : ℚ) : ℝ) ≤ stT297 240 := by
  have hc : ((693189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447451419933/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((693189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c241 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-45189/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5099199/10000000) (δ := 14861/1000000000) (ψ := -19999/50000) 297 259
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t241 : ((-29115252243/1000000000000 : ℚ) : ℝ) ≤ stT297 241 := by
  have hc : ((-45199/100000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29115252243/1000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-45199/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c242 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-991831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -376711/500000) (δ := 1871/125000000) (ψ := -19999/50000) 297 260
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t242 : ((-25505521803/400000000000 : ℚ) : ℝ) ≤ stT297 242 := by
  have hc : ((-991931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25505521803/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-991931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c243 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-216427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4472373/10000000) (δ := 3717/250000000) (ψ := -19999/50000) 297 260
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t243 : ((-138902287027/10000000000000 : ℚ) : ℝ) ≤ stT297 243 := by
  have hc : ((-216527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138902287027/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-216527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c244 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((210579/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711537/5000000) (δ := 3717/250000000) (ψ := -19999/50000) 297 260
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t244 : ((8424581371/156250000000 : ℚ) : ℝ) ≤ stT297 244 := by
  have hc : ((105277/125000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8424581371/156250000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((105277/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c245 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((99851/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806857/5000000) (δ := 3721/125000000) (ψ := -19999/50000) 297 260
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t245 : ((31892210763/625000000000 : ℚ) : ℝ) ≤ stT297 245 := by
  have hc : ((199677/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31892210763/625000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((199677/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c246 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-280653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144943/312500) (δ := 2987/200000000) (ψ := -19999/50000) 297 260
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t246 : ((-179001655481/10000000000000 : ℚ) : ℝ) ≤ stT297 246 := by
  have hc : ((-280753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179001655481/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-280753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c247 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-199337/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153007/200000) (δ := 2987/200000000) (ψ := -19999/50000) 297 260
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t247 : ((-25369573749/400000000000 : ℚ) : ℝ) ≤ stT297 247 := by
  have hc : ((-199357/200000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25369573749/400000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-199357/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c248 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((-436991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316101/625000) (δ := 119/8000000) (ψ := -19999/50000) 297 261
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t248 : ((-277553222091/10000000000000 : ℚ) : ℝ) ≤ stT297 248 := by
  have hc : ((-437091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277553222091/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-437091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c249 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((42277/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1034861/5000000) (δ := 933/62500000) (ψ := -19999/50000) 297 261
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t249 : ((26787988773/625000000000 : ℚ) : ℝ) ≤ stT297 249 := by
  have hc : ((169083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26787988773/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((169083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_c250 :
    |Real.cos (((297 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((935007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 226573/2500000) (δ := 3757/250000000) (ψ := -19999/50000) 297 261
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st297_t250 : ((118257321337/2000000000000 : ℚ) : ℝ) ≤ stT297 250 := by
  have hc : ((934907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((297 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st297_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118257321337/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((934907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st297_p1 : ((920969/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT297 (i+1) := by
  rw [Finset.sum_range_one]
  exact st297_t1

theorem st297_p2 : ((195923246169/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT297 (i+1))
      = (∑ i ∈ Finset.range 1, stT297 (i+1)) + stT297 2 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 1
    simpa using h
  have hprev := st297_p1
  have hstep := st297_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p3 : ((9153942175343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT297 (i+1))
      = (∑ i ∈ Finset.range 2, stT297 (i+1)) + stT297 3 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 2
    simpa using h
  have hprev := st297_p2
  have hstep := st297_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p4 : ((7063581757271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT297 (i+1))
      = (∑ i ∈ Finset.range 3, stT297 (i+1)) + stT297 4 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 3
    simpa using h
  have hprev := st297_p3
  have hstep := st297_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p5 : ((16972805375717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT297 (i+1))
      = (∑ i ∈ Finset.range 4, stT297 (i+1)) + stT297 5 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 4
    simpa using h
  have hprev := st297_p4
  have hstep := st297_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p6 : ((17186964216473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT297 (i+1))
      = (∑ i ∈ Finset.range 5, stT297 (i+1)) + stT297 6 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 5
    simpa using h
  have hprev := st297_p5
  have hstep := st297_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p7 : ((20816677298281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT297 (i+1))
      = (∑ i ∈ Finset.range 6, stT297 (i+1)) + stT297 7 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 6
    simpa using h
  have hprev := st297_p6
  have hstep := st297_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p8 : ((18617582221349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT297 (i+1))
      = (∑ i ∈ Finset.range 7, stT297 (i+1)) + stT297 8 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 7
    simpa using h
  have hprev := st297_p7
  have hstep := st297_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p9 : ((21580641925043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT297 (i+1))
      = (∑ i ∈ Finset.range 8, stT297 (i+1)) + stT297 9 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 8
    simpa using h
  have hprev := st297_p8
  have hstep := st297_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p10 : ((241912312419/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT297 (i+1))
      = (∑ i ∈ Finset.range 9, stT297 (i+1)) + stT297 10 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 9
    simpa using h
  have hprev := st297_p9
  have hstep := st297_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p11 : ((10823543547021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT297 (i+1))
      = (∑ i ∈ Finset.range 10, stT297 (i+1)) + stT297 11 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 10
    simpa using h
  have hprev := st297_p10
  have hstep := st297_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p12 : ((15031602269/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT297 (i+1))
      = (∑ i ∈ Finset.range 11, stT297 (i+1)) + stT297 12 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 11
    simpa using h
  have hprev := st297_p11
  have hstep := st297_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p13 : ((8914259010881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT297 (i+1))
      = (∑ i ∈ Finset.range 12, stT297 (i+1)) + stT297 13 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 12
    simpa using h
  have hprev := st297_p12
  have hstep := st297_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p14 : ((9400649005067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT297 (i+1))
      = (∑ i ∈ Finset.range 13, stT297 (i+1)) + stT297 14 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 13
    simpa using h
  have hprev := st297_p13
  have hstep := st297_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p15 : ((10566792266321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT297 (i+1))
      = (∑ i ∈ Finset.range 14, stT297 (i+1)) + stT297 15 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 14
    simpa using h
  have hprev := st297_p14
  have hstep := st297_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p16 : ((11471364766321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT297 (i+1))
      = (∑ i ∈ Finset.range 15, stT297 (i+1)) + stT297 16 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 15
    simpa using h
  have hprev := st297_p15
  have hstep := st297_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p17 : ((12679798393321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT297 (i+1))
      = (∑ i ∈ Finset.range 16, stT297 (i+1)) + stT297 17 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 16
    simpa using h
  have hprev := st297_p16
  have hstep := st297_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p18 : ((24473721477207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT297 (i+1))
      = (∑ i ∈ Finset.range 17, stT297 (i+1)) + stT297 18 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 17
    simpa using h
  have hprev := st297_p17
  have hstep := st297_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p19 : ((785735811/320000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT297 (i+1))
      = (∑ i ∈ Finset.range 18, stT297 (i+1)) + stT297 19 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 18
    simpa using h
  have hprev := st297_p18
  have hstep := st297_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p20 : ((11732129665371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT297 (i+1))
      = (∑ i ∈ Finset.range 19, stT297 (i+1)) + stT297 20 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 19
    simpa using h
  have hprev := st297_p19
  have hstep := st297_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p21 : ((400310594411/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT297 (i+1))
      = (∑ i ∈ Finset.range 20, stT297 (i+1)) + stT297 21 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 20
    simpa using h
  have hprev := st297_p20
  have hstep := st297_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p22 : ((13298554517419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT297 (i+1))
      = (∑ i ∈ Finset.range 21, stT297 (i+1)) + stT297 22 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 21
    simpa using h
  have hprev := st297_p21
  have hstep := st297_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p23 : ((3283203149201/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT297 (i+1))
      = (∑ i ∈ Finset.range 22, stT297 (i+1)) + stT297 23 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 22
    simpa using h
  have hprev := st297_p22
  have hstep := st297_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p24 : ((3224168389319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT297 (i+1))
      = (∑ i ∈ Finset.range 23, stT297 (i+1)) + stT297 24 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 23
    simpa using h
  have hprev := st297_p23
  have hstep := st297_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p25 : ((3275978389319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT297 (i+1))
      = (∑ i ∈ Finset.range 24, stT297 (i+1)) + stT297 25 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 24
    simpa using h
  have hprev := st297_p24
  have hstep := st297_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p26 : ((13989269884921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT297 (i+1))
      = (∑ i ∈ Finset.range 25, stT297 (i+1)) + stT297 26 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 25
    simpa using h
  have hprev := st297_p25
  have hstep := st297_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p27 : ((14577176729671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT297 (i+1))
      = (∑ i ∈ Finset.range 26, stT297 (i+1)) + stT297 27 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 26
    simpa using h
  have hprev := st297_p26
  have hstep := st297_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p28 : ((13731673699117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT297 (i+1))
      = (∑ i ∈ Finset.range 27, stT297 (i+1)) + stT297 28 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 27
    simpa using h
  have hprev := st297_p27
  have hstep := st297_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p29 : ((27667777497051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT297 (i+1))
      = (∑ i ∈ Finset.range 28, stT297 (i+1)) + stT297 29 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 28
    simpa using h
  have hprev := st297_p28
  have hstep := st297_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p30 : ((3574520164791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT297 (i+1))
      = (∑ i ∈ Finset.range 29, stT297 (i+1)) + stT297 30 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 29
    simpa using h
  have hprev := st297_p29
  have hstep := st297_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p31 : ((2724975482539/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT297 (i+1))
      = (∑ i ∈ Finset.range 30, stT297 (i+1)) + stT297 31 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 30
    simpa using h
  have hprev := st297_p30
  have hstep := st297_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p32 : ((89312357957/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT297 (i+1))
      = (∑ i ∈ Finset.range 31, stT297 (i+1)) + stT297 32 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 31
    simpa using h
  have hprev := st297_p31
  have hstep := st297_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p33 : ((1727859757783/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT297 (i+1))
      = (∑ i ∈ Finset.range 32, stT297 (i+1)) + stT297 33 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 32
    simpa using h
  have hprev := st297_p32
  have hstep := st297_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p34 : ((27659155302333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT297 (i+1))
      = (∑ i ∈ Finset.range 33, stT297 (i+1)) + stT297 34 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 33
    simpa using h
  have hprev := st297_p33
  have hstep := st297_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p35 : ((5776085299329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT297 (i+1))
      = (∑ i ∈ Finset.range 34, stT297 (i+1)) + stT297 35 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 34
    simpa using h
  have hprev := st297_p34
  have hstep := st297_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p36 : ((1091419713773/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT297 (i+1))
      = (∑ i ∈ Finset.range 35, stT297 (i+1)) + stT297 36 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 35
    simpa using h
  have hprev := st297_p35
  have hstep := st297_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p37 : ((43626854781/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT297 (i+1))
      = (∑ i ∈ Finset.range 36, stT297 (i+1)) + stT297 37 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 36
    simpa using h
  have hprev := st297_p36
  have hstep := st297_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p38 : ((28886365384803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT297 (i+1))
      = (∑ i ∈ Finset.range 37, stT297 (i+1)) + stT297 38 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 37
    simpa using h
  have hprev := st297_p37
  have hstep := st297_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p39 : ((7255164203967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT297 (i+1))
      = (∑ i ∈ Finset.range 38, stT297 (i+1)) + stT297 39 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 38
    simpa using h
  have hprev := st297_p38
  have hstep := st297_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p40 : ((27575914771703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT297 (i+1))
      = (∑ i ∈ Finset.range 39, stT297 (i+1)) + stT297 40 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 39
    simpa using h
  have hprev := st297_p39
  have hstep := st297_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p41 : ((26315542230087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT297 (i+1))
      = (∑ i ∈ Finset.range 40, stT297 (i+1)) + stT297 41 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 40
    simpa using h
  have hprev := st297_p40
  have hstep := st297_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p42 : ((26214950300593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT297 (i+1))
      = (∑ i ∈ Finset.range 41, stT297 (i+1)) + stT297 42 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 41
    simpa using h
  have hprev := st297_p41
  have hstep := st297_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p43 : ((13562900483159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT297 (i+1))
      = (∑ i ∈ Finset.range 42, stT297 (i+1)) + stT297 43 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 42
    simpa using h
  have hprev := st297_p42
  have hstep := st297_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p44 : ((14261180824131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT297 (i+1))
      = (∑ i ∈ Finset.range 43, stT297 (i+1)) + stT297 44 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 43
    simpa using h
  have hprev := st297_p43
  have hstep := st297_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p45 : ((3751612838401/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT297 (i+1))
      = (∑ i ∈ Finset.range 44, stT297 (i+1)) + stT297 45 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 44
    simpa using h
  have hprev := st297_p44
  have hstep := st297_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p46 : ((3930170876977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT297 (i+1))
      = (∑ i ∈ Finset.range 45, stT297 (i+1)) + stT297 46 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 45
    simpa using h
  have hprev := st297_p45
  have hstep := st297_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p47 : ((32809371191009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT297 (i+1))
      = (∑ i ∈ Finset.range 46, stT297 (i+1)) + stT297 47 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 46
    simpa using h
  have hprev := st297_p46
  have hstep := st297_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p48 : ((17088801322567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT297 (i+1))
      = (∑ i ∈ Finset.range 47, stT297 (i+1)) + stT297 48 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 47
    simpa using h
  have hprev := st297_p47
  have hstep := st297_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p49 : ((7117349301621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT297 (i+1))
      = (∑ i ∈ Finset.range 48, stT297 (i+1)) + stT297 49 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 48
    simpa using h
  have hprev := st297_p48
  have hstep := st297_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p50 : ((36990907282101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT297 (i+1))
      = (∑ i ∈ Finset.range 49, stT297 (i+1)) + stT297 50 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 49
    simpa using h
  have hprev := st297_p49
  have hstep := st297_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p51 : ((38205769205901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT297 (i+1))
      = (∑ i ∈ Finset.range 50, stT297 (i+1)) + stT297 51 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 50
    simpa using h
  have hprev := st297_p50
  have hstep := st297_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p52 : ((38912077036401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT297 (i+1))
      = (∑ i ∈ Finset.range 51, stT297 (i+1)) + stT297 52 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 51
    simpa using h
  have hprev := st297_p51
  have hstep := st297_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p53 : ((38786632468451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT297 (i+1))
      = (∑ i ∈ Finset.range 52, stT297 (i+1)) + stT297 53 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 52
    simpa using h
  have hprev := st297_p52
  have hstep := st297_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p54 : ((37788767234267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT297 (i+1))
      = (∑ i ∈ Finset.range 53, stT297 (i+1)) + stT297 54 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 53
    simpa using h
  have hprev := st297_p53
  have hstep := st297_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p55 : ((36445179673867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT297 (i+1))
      = (∑ i ∈ Finset.range 54, stT297 (i+1)) + stT297 55 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 54
    simpa using h
  have hprev := st297_p54
  have hstep := st297_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p56 : ((7148537685839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT297 (i+1))
      = (∑ i ∈ Finset.range 55, stT297 (i+1)) + stT297 56 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 55
    simpa using h
  have hprev := st297_p55
  have hstep := st297_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p57 : ((36345945204063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT297 (i+1))
      = (∑ i ∈ Finset.range 56, stT297 (i+1)) + stT297 57 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 56
    simpa using h
  have hprev := st297_p56
  have hstep := st297_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p58 : ((37658615284863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT297 (i+1))
      = (∑ i ∈ Finset.range 57, stT297 (i+1)) + stT297 58 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 57
    simpa using h
  have hprev := st297_p57
  have hstep := st297_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p59 : ((952458305007/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT297 (i+1))
      = (∑ i ∈ Finset.range 58, stT297 (i+1)) + stT297 59 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 58
    simpa using h
  have hprev := st297_p58
  have hstep := st297_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p60 : ((7410092766731/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT297 (i+1))
      = (∑ i ∈ Finset.range 59, stT297 (i+1)) + stT297 60 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 59
    simpa using h
  have hprev := st297_p59
  have hstep := st297_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p61 : ((18056764745447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT297 (i+1))
      = (∑ i ∈ Finset.range 60, stT297 (i+1)) + stT297 61 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 60
    simpa using h
  have hprev := st297_p60
  have hstep := st297_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p62 : ((23040464189/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT297 (i+1))
      = (∑ i ∈ Finset.range 61, stT297 (i+1)) + stT297 62 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 61
    simpa using h
  have hprev := st297_p61
  have hstep := st297_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p63 : ((37909170192709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT297 (i+1))
      = (∑ i ∈ Finset.range 62, stT297 (i+1)) + stT297 63 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 62
    simpa using h
  have hprev := st297_p62
  have hstep := st297_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p64 : ((37174167104707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT297 (i+1))
      = (∑ i ∈ Finset.range 63, stT297 (i+1)) + stT297 64 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 63
    simpa using h
  have hprev := st297_p63
  have hstep := st297_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p65 : ((7250966962187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT297 (i+1))
      = (∑ i ∈ Finset.range 64, stT297 (i+1)) + stT297 65 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 64
    simpa using h
  have hprev := st297_p64
  have hstep := st297_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p66 : ((37229572220169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT297 (i+1))
      = (∑ i ∈ Finset.range 65, stT297 (i+1)) + stT297 66 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 65
    simpa using h
  have hprev := st297_p65
  have hstep := st297_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p67 : ((37717119753219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT297 (i+1))
      = (∑ i ∈ Finset.range 66, stT297 (i+1)) + stT297 67 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 66
    simpa using h
  have hprev := st297_p66
  have hstep := st297_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p68 : ((3651017551221/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT297 (i+1))
      = (∑ i ∈ Finset.range 67, stT297 (i+1)) + stT297 68 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 67
    simpa using h
  have hprev := st297_p67
  have hstep := st297_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p69 : ((18420350974629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT297 (i+1))
      = (∑ i ∈ Finset.range 68, stT297 (i+1)) + stT297 69 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 68
    simpa using h
  have hprev := st297_p68
  have hstep := st297_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p70 : ((754827654837/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT297 (i+1))
      = (∑ i ∈ Finset.range 69, stT297 (i+1)) + stT297 70 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 69
    simpa using h
  have hprev := st297_p69
  have hstep := st297_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p71 : ((18314046701991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT297 (i+1))
      = (∑ i ∈ Finset.range 70, stT297 (i+1)) + stT297 71 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 70
    simpa using h
  have hprev := st297_p70
  have hstep := st297_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p72 : ((9216798018171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT297 (i+1))
      = (∑ i ∈ Finset.range 71, stT297 (i+1)) + stT297 72 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 71
    simpa using h
  have hprev := st297_p71
  have hstep := st297_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p73 : ((37665399500163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT297 (i+1))
      = (∑ i ∈ Finset.range 72, stT297 (i+1)) + stT297 73 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 72
    simpa using h
  have hprev := st297_p72
  have hstep := st297_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p74 : ((7301288031113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT297 (i+1))
      = (∑ i ∈ Finset.range 73, stT297 (i+1)) + stT297 74 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 73
    simpa using h
  have hprev := st297_p73
  have hstep := st297_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p75 : ((7440407903693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT297 (i+1))
      = (∑ i ∈ Finset.range 74, stT297 (i+1)) + stT297 75 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 74
    simpa using h
  have hprev := st297_p74
  have hstep := st297_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p76 : ((37368341739827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT297 (i+1))
      = (∑ i ∈ Finset.range 75, stT297 (i+1)) + stT297 76 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 75
    simpa using h
  have hprev := st297_p75
  have hstep := st297_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p77 : ((36485249654367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT297 (i+1))
      = (∑ i ∈ Finset.range 76, stT297 (i+1)) + stT297 77 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 76
    simpa using h
  have hprev := st297_p76
  have hstep := st297_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p78 : ((37617390781127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT297 (i+1))
      = (∑ i ∈ Finset.range 77, stT297 (i+1)) + stT297 78 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 77
    simpa using h
  have hprev := st297_p77
  have hstep := st297_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p79 : ((36720407622599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT297 (i+1))
      = (∑ i ∈ Finset.range 78, stT297 (i+1)) + stT297 79 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 78
    simpa using h
  have hprev := st297_p78
  have hstep := st297_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p80 : ((37080745186367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT297 (i+1))
      = (∑ i ∈ Finset.range 79, stT297 (i+1)) + stT297 80 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 79
    simpa using h
  have hprev := st297_p79
  have hstep := st297_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p81 : ((7464541921323/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT297 (i+1))
      = (∑ i ∈ Finset.range 80, stT297 (i+1)) + stT297 81 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 80
    simpa using h
  have hprev := st297_p80
  have hstep := st297_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p82 : ((7318511590747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT297 (i+1))
      = (∑ i ∈ Finset.range 81, stT297 (i+1)) + stT297 82 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 81
    simpa using h
  have hprev := st297_p81
  have hstep := st297_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p83 : ((7521527064499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT297 (i+1))
      = (∑ i ∈ Finset.range 82, stT297 (i+1)) + stT297 83 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 82
    simpa using h
  have hprev := st297_p82
  have hstep := st297_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p84 : ((7303356854241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT297 (i+1))
      = (∑ i ∈ Finset.range 83, stT297 (i+1)) + stT297 84 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 83
    simpa using h
  have hprev := st297_p83
  have hstep := st297_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p85 : ((37516344237153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT297 (i+1))
      = (∑ i ∈ Finset.range 84, stT297 (i+1)) + stT297 85 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 84
    simpa using h
  have hprev := st297_p84
  have hstep := st297_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p86 : ((36713130059793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT297 (i+1))
      = (∑ i ∈ Finset.range 85, stT297 (i+1)) + stT297 86 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 85
    simpa using h
  have hprev := st297_p85
  have hstep := st297_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p87 : ((37271751873169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT297 (i+1))
      = (∑ i ∈ Finset.range 86, stT297 (i+1)) + stT297 87 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 86
    simpa using h
  have hprev := st297_p86
  have hstep := st297_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p88 : ((36961241964033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT297 (i+1))
      = (∑ i ∈ Finset.range 87, stT297 (i+1)) + stT297 88 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 87
    simpa using h
  have hprev := st297_p87
  have hstep := st297_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p89 : ((18523506870641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT297 (i+1))
      = (∑ i ∈ Finset.range 88, stT297 (i+1)) + stT297 89 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 88
    simpa using h
  have hprev := st297_p88
  have hstep := st297_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p90 : ((18573853466837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT297 (i+1))
      = (∑ i ∈ Finset.range 89, stT297 (i+1)) + stT297 90 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 89
    simpa using h
  have hprev := st297_p89
  have hstep := st297_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p91 : ((36902512023889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT297 (i+1))
      = (∑ i ∈ Finset.range 90, stT297 (i+1)) + stT297 91 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 90
    simpa using h
  have hprev := st297_p90
  have hstep := st297_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p92 : ((37250406831997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT297 (i+1))
      = (∑ i ∈ Finset.range 91, stT297 (i+1)) + stT297 92 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 91
    simpa using h
  have hprev := st297_p91
  have hstep := st297_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p93 : ((36837378480877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT297 (i+1))
      = (∑ i ∈ Finset.range 92, stT297 (i+1)) + stT297 93 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 92
    simpa using h
  have hprev := st297_p92
  have hstep := st297_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p94 : ((18640385448731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT297 (i+1))
      = (∑ i ∈ Finset.range 93, stT297 (i+1)) + stT297 94 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 93
    simpa using h
  have hprev := st297_p93
  have hstep := st297_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p95 : ((2302394840857/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT297 (i+1))
      = (∑ i ∈ Finset.range 94, stT297 (i+1)) + stT297 95 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 94
    simpa using h
  have hprev := st297_p94
  have hstep := st297_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p96 : ((2328057820447/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT297 (i+1))
      = (∑ i ∈ Finset.range 95, stT297 (i+1)) + stT297 96 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 95
    simpa using h
  have hprev := st297_p95
  have hstep := st297_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p97 : ((4612546085777/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT297 (i+1))
      = (∑ i ∈ Finset.range 96, stT297 (i+1)) + stT297 97 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 96
    simpa using h
  have hprev := st297_p96
  have hstep := st297_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p98 : ((4644371682151/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT297 (i+1))
      = (∑ i ∈ Finset.range 97, stT297 (i+1)) + stT297 98 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 97
    simpa using h
  have hprev := st297_p97
  have hstep := st297_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p99 : ((18513007008157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT297 (i+1))
      = (∑ i ∈ Finset.range 98, stT297 (i+1)) + stT297 99 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 98
    simpa using h
  have hprev := st297_p98
  have hstep := st297_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p100 : ((18498916008157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT297 (i+1))
      = (∑ i ∈ Finset.range 99, stT297 (i+1)) + stT297 100 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 99
    simpa using h
  have hprev := st297_p99
  have hstep := st297_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p101 : ((37209447530141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT297 (i+1))
      = (∑ i ∈ Finset.range 100, stT297 (i+1)) + stT297 101 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 100
    simpa using h
  have hprev := st297_p100
  have hstep := st297_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p102 : ((7359340471209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT297 (i+1))
      = (∑ i ∈ Finset.range 101, stT297 (i+1)) + stT297 102 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 101
    simpa using h
  have hprev := st297_p101
  have hstep := st297_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p103 : ((37411486561647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT297 (i+1))
      = (∑ i ∈ Finset.range 102, stT297 (i+1)) + stT297 103 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 102
    simpa using h
  have hprev := st297_p102
  have hstep := st297_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p104 : ((18308054437849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT297 (i+1))
      = (∑ i ∈ Finset.range 103, stT297 (i+1)) + stT297 104 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 103
    simpa using h
  have hprev := st297_p103
  have hstep := st297_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p105 : ((18770343635299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT297 (i+1))
      = (∑ i ∈ Finset.range 104, stT297 (i+1)) + stT297 105 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 104
    simpa using h
  have hprev := st297_p104
  have hstep := st297_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p106 : ((18284652070999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT297 (i+1))
      = (∑ i ∈ Finset.range 105, stT297 (i+1)) + stT297 106 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 105
    simpa using h
  have hprev := st297_p105
  have hstep := st297_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p107 : ((18738032403647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT297 (i+1))
      = (∑ i ∈ Finset.range 106, stT297 (i+1)) + stT297 107 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 106
    simpa using h
  have hprev := st297_p106
  have hstep := st297_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p108 : ((7352116807699/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT297 (i+1))
      = (∑ i ∈ Finset.range 107, stT297 (i+1)) + stT297 108 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 107
    simpa using h
  have hprev := st297_p107
  have hstep := st297_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p109 : ((37163213860203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT297 (i+1))
      = (∑ i ∈ Finset.range 108, stT297 (i+1)) + stT297 109 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 108
    simpa using h
  have hprev := st297_p108
  have hstep := st297_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p110 : ((9289657164159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT297 (i+1))
      = (∑ i ∈ Finset.range 109, stT297 (i+1)) + stT297 110 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 109
    simpa using h
  have hprev := st297_p109
  have hstep := st297_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p111 : ((918662084289/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT297 (i+1))
      = (∑ i ∈ Finset.range 110, stT297 (i+1)) + stT297 111 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 110
    simpa using h
  have hprev := st297_p110
  have hstep := st297_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p112 : ((4687767504649/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT297 (i+1))
      = (∑ i ∈ Finset.range 111, stT297 (i+1)) + stT297 112 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 111
    simpa using h
  have hprev := st297_p111
  have hstep := st297_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p113 : ((36570827187913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT297 (i+1))
      = (∑ i ∈ Finset.range 112, stT297 (i+1)) + stT297 113 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 112
    simpa using h
  have hprev := st297_p112
  have hstep := st297_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p114 : ((18719802185249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT297 (i+1))
      = (∑ i ∈ Finset.range 113, stT297 (i+1)) + stT297 114 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 113
    simpa using h
  have hprev := st297_p113
  have hstep := st297_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p115 : ((36882232144423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT297 (i+1))
      = (∑ i ∈ Finset.range 114, stT297 (i+1)) + stT297 115 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 114
    simpa using h
  have hprev := st297_p114
  have hstep := st297_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p116 : ((36947410231147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT297 (i+1))
      = (∑ i ∈ Finset.range 115, stT297 (i+1)) + stT297 116 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 115
    simpa using h
  have hprev := st297_p115
  have hstep := st297_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p117 : ((37408164390147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT297 (i+1))
      = (∑ i ∈ Finset.range 116, stT297 (i+1)) + stT297 117 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 116
    simpa using h
  have hprev := st297_p116
  have hstep := st297_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p118 : ((36573243370447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT297 (i+1))
      = (∑ i ∈ Finset.range 117, stT297 (i+1)) + stT297 118 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 117
    simpa using h
  have hprev := st297_p117
  have hstep := st297_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p119 : ((37471534074607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT297 (i+1))
      = (∑ i ∈ Finset.range 118, stT297 (i+1)) + stT297 119 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 118
    simpa using h
  have hprev := st297_p118
  have hstep := st297_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p120 : ((36873393609277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT297 (i+1))
      = (∑ i ∈ Finset.range 119, stT297 (i+1)) + stT297 120 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 119
    simpa using h
  have hprev := st297_p119
  have hstep := st297_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p121 : ((36907389938917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT297 (i+1))
      = (∑ i ∈ Finset.range 120, stT297 (i+1)) + stT297 121 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 120
    simpa using h
  have hprev := st297_p120
  have hstep := st297_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p122 : ((7492424780277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT297 (i+1))
      = (∑ i ∈ Finset.range 121, stT297 (i+1)) + stT297 122 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 121
    simpa using h
  have hprev := st297_p121
  have hstep := st297_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p123 : ((7315458157059/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT297 (i+1))
      = (∑ i ∈ Finset.range 122, stT297 (i+1)) + stT297 123 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 122
    simpa using h
  have hprev := st297_p122
  have hstep := st297_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p124 : ((37346219261613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT297 (i+1))
      = (∑ i ∈ Finset.range 123, stT297 (i+1)) + stT297 124 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 123
    simpa using h
  have hprev := st297_p123
  have hstep := st297_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p125 : ((1484229340433/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT297 (i+1))
      = (∑ i ∈ Finset.range 124, stT297 (i+1)) + stT297 125 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 124
    simpa using h
  have hprev := st297_p124
  have hstep := st297_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p126 : ((36676257073919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT297 (i+1))
      = (∑ i ∈ Finset.range 125, stT297 (i+1)) + stT297 126 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 125
    simpa using h
  have hprev := st297_p125
  have hstep := st297_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p127 : ((37530399338839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT297 (i+1))
      = (∑ i ∈ Finset.range 126, stT297 (i+1)) + stT297 127 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 126
    simpa using h
  have hprev := st297_p126
  have hstep := st297_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p128 : ((36771317107987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT297 (i+1))
      = (∑ i ∈ Finset.range 127, stT297 (i+1)) + stT297 128 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 127
    simpa using h
  have hprev := st297_p127
  have hstep := st297_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p129 : ((36948263785837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT297 (i+1))
      = (∑ i ∈ Finset.range 128, stT297 (i+1)) + stT297 129 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 128
    simpa using h
  have hprev := st297_p128
  have hstep := st297_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p130 : ((37475956256233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT297 (i+1))
      = (∑ i ∈ Finset.range 129, stT297 (i+1)) + stT297 130 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 129
    simpa using h
  have hprev := st297_p129
  have hstep := st297_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p131 : ((36603703353943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT297 (i+1))
      = (∑ i ∈ Finset.range 130, stT297 (i+1)) + stT297 131 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 130
    simpa using h
  have hprev := st297_p130
  have hstep := st297_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p132 : ((37195088480543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT297 (i+1))
      = (∑ i ∈ Finset.range 131, stT297 (i+1)) + stT297 132 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 131
    simpa using h
  have hprev := st297_p131
  have hstep := st297_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p133 : ((4665885952063/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT297 (i+1))
      = (∑ i ∈ Finset.range 132, stT297 (i+1)) + stT297 133 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 132
    simpa using h
  have hprev := st297_p132
  have hstep := st297_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p134 : ((18284650000983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT297 (i+1))
      = (∑ i ∈ Finset.range 133, stT297 (i+1)) + stT297 134 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 133
    simpa using h
  have hprev := st297_p133
  have hstep := st297_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p135 : ((18675329441981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT297 (i+1))
      = (∑ i ∈ Finset.range 134, stT297 (i+1)) + stT297 135 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 134
    simpa using h
  have hprev := st297_p134
  have hstep := st297_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p136 : ((37189737460117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT297 (i+1))
      = (∑ i ∈ Finset.range 135, stT297 (i+1)) + stT297 136 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 135
    simpa using h
  have hprev := st297_p135
  have hstep := st297_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p137 : ((36590589010087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT297 (i+1))
      = (∑ i ∈ Finset.range 136, stT297 (i+1)) + stT297 137 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 136
    simpa using h
  have hprev := st297_p136
  have hstep := st297_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p138 : ((37426782886423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT297 (i+1))
      = (∑ i ∈ Finset.range 137, stT297 (i+1)) + stT297 138 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 137
    simpa using h
  have hprev := st297_p137
  have hstep := st297_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p139 : ((18553773723963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT297 (i+1))
      = (∑ i ∈ Finset.range 138, stT297 (i+1)) + stT297 139 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 138
    simpa using h
  have hprev := st297_p138
  have hstep := st297_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p140 : ((9152936852259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT297 (i+1))
      = (∑ i ∈ Finset.range 139, stT297 (i+1)) + stT297 140 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 139
    simpa using h
  have hprev := st297_p139
  have hstep := st297_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p141 : ((7490173164657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT297 (i+1))
      = (∑ i ∈ Finset.range 140, stT297 (i+1)) + stT297 141 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 140
    simpa using h
  have hprev := st297_p140
  have hstep := st297_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p142 : ((37089961338091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT297 (i+1))
      = (∑ i ∈ Finset.range 141, stT297 (i+1)) + stT297 142 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 141
    simpa using h
  have hprev := st297_p141
  have hstep := st297_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p143 : ((36608828928041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT297 (i+1))
      = (∑ i ∈ Finset.range 142, stT297 (i+1)) + stT297 143 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 142
    simpa using h
  have hprev := st297_p142
  have hstep := st297_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p144 : ((18718333048453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT297 (i+1))
      = (∑ i ∈ Finset.range 143, stT297 (i+1)) + stT297 144 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 143
    simpa using h
  have hprev := st297_p143
  have hstep := st297_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p145 : ((4641980467327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT297 (i+1))
      = (∑ i ∈ Finset.range 144, stT297 (i+1)) + stT297 145 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 144
    simpa using h
  have hprev := st297_p144
  have hstep := st297_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p146 : ((18291995132287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT297 (i+1))
      = (∑ i ∈ Finset.range 145, stT297 (i+1)) + stT297 146 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 145
    simpa using h
  have hprev := st297_p145
  have hstep := st297_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p147 : ((4672260644091/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT297 (i+1))
      = (∑ i ∈ Finset.range 146, stT297 (i+1)) + stT297 147 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 146
    simpa using h
  have hprev := st297_p146
  have hstep := st297_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p148 : ((37239349658623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT297 (i+1))
      = (∑ i ∈ Finset.range 147, stT297 (i+1)) + stT297 148 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 147
    simpa using h
  have hprev := st297_p147
  have hstep := st297_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p149 : ((36562535407199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT297 (i+1))
      = (∑ i ∈ Finset.range 148, stT297 (i+1)) + stT297 149 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 148
    simpa using h
  have hprev := st297_p148
  have hstep := st297_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p150 : ((1490233898887/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT297 (i+1))
      = (∑ i ∈ Finset.range 149, stT297 (i+1)) + stT297 150 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 149
    simpa using h
  have hprev := st297_p149
  have hstep := st297_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p151 : ((7476057572839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT297 (i+1))
      = (∑ i ∈ Finset.range 150, stT297 (i+1)) + stT297 151 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 150
    simpa using h
  have hprev := st297_p150
  have hstep := st297_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p152 : ((36591580233831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT297 (i+1))
      = (∑ i ∈ Finset.range 151, stT297 (i+1)) + stT297 152 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 151
    simpa using h
  have hprev := st297_p151
  have hstep := st297_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p153 : ((37056452260611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT297 (i+1))
      = (∑ i ∈ Finset.range 152, stT297 (i+1)) + stT297 153 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 152
    simpa using h
  have hprev := st297_p152
  have hstep := st297_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p154 : ((37507362853863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT297 (i+1))
      = (∑ i ∈ Finset.range 153, stT297 (i+1)) + stT297 154 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 153
    simpa using h
  have hprev := st297_p153
  have hstep := st297_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p155 : ((36727553503983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT297 (i+1))
      = (∑ i ∈ Finset.range 154, stT297 (i+1)) + stT297 155 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 154
    simpa using h
  have hprev := st297_p154
  have hstep := st297_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p156 : ((36804802453743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT297 (i+1))
      = (∑ i ∈ Finset.range 155, stT297 (i+1)) + stT297 156 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 155
    simpa using h
  have hprev := st297_p155
  have hstep := st297_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p157 : ((37532233900163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT297 (i+1))
      = (∑ i ∈ Finset.range 156, stT297 (i+1)) + stT297 157 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 156
    simpa using h
  have hprev := st297_p156
  have hstep := st297_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p158 : ((36996527418587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT297 (i+1))
      = (∑ i ∈ Finset.range 157, stT297 (i+1)) + stT297 158 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 157
    simpa using h
  have hprev := st297_p157
  have hstep := st297_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p159 : ((36596125773463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT297 (i+1))
      = (∑ i ∈ Finset.range 158, stT297 (i+1)) + stT297 159 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 158
    simpa using h
  have hprev := st297_p158
  have hstep := st297_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p160 : ((37364356455799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT297 (i+1))
      = (∑ i ∈ Finset.range 159, stT297 (i+1)) + stT297 160 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 159
    simpa using h
  have hprev := st297_p159
  have hstep := st297_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p161 : ((37331342486009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT297 (i+1))
      = (∑ i ∈ Finset.range 160, stT297 (i+1)) + stT297 161 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 160
    simpa using h
  have hprev := st297_p160
  have hstep := st297_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p162 : ((18291522987067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT297 (i+1))
      = (∑ i ∈ Finset.range 161, stT297 (i+1)) + stT297 162 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 161
    simpa using h
  have hprev := st297_p161
  have hstep := st297_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p163 : ((18501810673717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT297 (i+1))
      = (∑ i ∈ Finset.range 162, stT297 (i+1)) + stT297 163 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 162
    simpa using h
  have hprev := st297_p162
  have hstep := st297_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p164 : ((3754044623313/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT297 (i+1))
      = (∑ i ∈ Finset.range 163, stT297 (i+1)) + stT297 164 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 163
    simpa using h
  have hprev := st297_p163
  have hstep := st297_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p165 : ((18433059870659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT297 (i+1))
      = (∑ i ∈ Finset.range 164, stT297 (i+1)) + stT297 165 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 164
    simpa using h
  have hprev := st297_p164
  have hstep := st297_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p166 : ((36636892081129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT297 (i+1))
      = (∑ i ∈ Finset.range 165, stT297 (i+1)) + stT297 166 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 165
    simpa using h
  have hprev := st297_p165
  have hstep := st297_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p167 : ((4675966499183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT297 (i+1))
      = (∑ i ∈ Finset.range 166, stT297 (i+1)) + stT297 167 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 166
    simpa using h
  have hprev := st297_p166
  have hstep := st297_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p168 : ((37318641067889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT297 (i+1))
      = (∑ i ∈ Finset.range 167, stT297 (i+1)) + stT297 168 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 167
    simpa using h
  have hprev := st297_p167
  have hstep := st297_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p169 : ((36585408540227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT297 (i+1))
      = (∑ i ∈ Finset.range 168, stT297 (i+1)) + stT297 169 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 168
    simpa using h
  have hprev := st297_p168
  have hstep := st297_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p170 : ((36945531117679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT297 (i+1))
      = (∑ i ∈ Finset.range 169, stT297 (i+1)) + stT297 170 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 169
    simpa using h
  have hprev := st297_p169
  have hstep := st297_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p171 : ((18774782533621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT297 (i+1))
      = (∑ i ∈ Finset.range 170, stT297 (i+1)) + stT297 171 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 170
    simpa using h
  have hprev := st297_p170
  have hstep := st297_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p172 : ((18495736020383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT297 (i+1))
      = (∑ i ∈ Finset.range 171, stT297 (i+1)) + stT297 172 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 171
    simpa using h
  have hprev := st297_p171
  have hstep := st297_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p173 : ((18281414438127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT297 (i+1))
      = (∑ i ∈ Finset.range 172, stT297 (i+1)) + stT297 173 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 172
    simpa using h
  have hprev := st297_p172
  have hstep := st297_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p174 : ((18621389551011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT297 (i+1))
      = (∑ i ∈ Finset.range 173, stT297 (i+1)) + stT297 174 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 173
    simpa using h
  have hprev := st297_p173
  have hstep := st297_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p175 : ((18742613566767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT297 (i+1))
      = (∑ i ∈ Finset.range 174, stT297 (i+1)) + stT297 175 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 174
    simpa using h
  have hprev := st297_p174
  have hstep := st297_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p176 : ((9186792613979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT297 (i+1))
      = (∑ i ∈ Finset.range 175, stT297 (i+1)) + stT297 176 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 175
    simpa using h
  have hprev := st297_p175
  have hstep := st297_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p177 : ((7335436469761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT297 (i+1))
      = (∑ i ∈ Finset.range 176, stT297 (i+1)) + stT297 177 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 176
    simpa using h
  have hprev := st297_p176
  have hstep := st297_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p178 : ((2339162885367/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT297 (i+1))
      = (∑ i ∈ Finset.range 177, stT297 (i+1)) + stT297 178 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 177
    simpa using h
  have hprev := st297_p177
  have hstep := st297_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p179 : ((186750709841/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT297 (i+1))
      = (∑ i ∈ Finset.range 178, stT297 (i+1)) + stT297 179 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 178
    simpa using h
  have hprev := st297_p178
  have hstep := st297_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p180 : ((915439779607/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT297 (i+1))
      = (∑ i ∈ Finset.range 179, stT297 (i+1)) + stT297 180 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 179
    simpa using h
  have hprev := st297_p179
  have hstep := st297_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p181 : ((4601148574009/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT297 (i+1))
      = (∑ i ∈ Finset.range 180, stT297 (i+1)) + stT297 181 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 180
    simpa using h
  have hprev := st297_p180
  have hstep := st297_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p182 : ((37511235156209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT297 (i+1))
      = (∑ i ∈ Finset.range 181, stT297 (i+1)) + stT297 182 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 181
    simpa using h
  have hprev := st297_p181
  have hstep := st297_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p183 : ((37234921364829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT297 (i+1))
      = (∑ i ∈ Finset.range 182, stT297 (i+1)) + stT297 183 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 182
    simpa using h
  have hprev := st297_p182
  have hstep := st297_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p184 : ((36564969981969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT297 (i+1))
      = (∑ i ∈ Finset.range 183, stT297 (i+1)) + stT297 184 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 183
    simpa using h
  have hprev := st297_p183
  have hstep := st297_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p185 : ((36897663139537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT297 (i+1))
      = (∑ i ∈ Finset.range 184, stT297 (i+1)) + stT297 185 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 184
    simpa using h
  have hprev := st297_p184
  have hstep := st297_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p186 : ((37541076852037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT297 (i+1))
      = (∑ i ∈ Finset.range 185, stT297 (i+1)) + stT297 186 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 185
    simpa using h
  have hprev := st297_p185
  have hstep := st297_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p187 : ((3717658186919/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT297 (i+1))
      = (∑ i ∈ Finset.range 186, stT297 (i+1)) + stT297 187 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 186
    simpa using h
  have hprev := st297_p186
  have hstep := st297_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p188 : ((3654904730079/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT297 (i+1))
      = (∑ i ∈ Finset.range 187, stT297 (i+1)) + stT297 188 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 187
    simpa using h
  have hprev := st297_p187
  have hstep := st297_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p189 : ((18461380835403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT297 (i+1))
      = (∑ i ∈ Finset.range 188, stT297 (i+1)) + stT297 189 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 188
    simpa using h
  have hprev := st297_p188
  have hstep := st297_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p190 : ((18773180626277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT297 (i+1))
      = (∑ i ∈ Finset.range 189, stT297 (i+1)) + stT297 190 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 189
    simpa using h
  have hprev := st297_p189
  have hstep := st297_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p191 : ((4647996648163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT297 (i+1))
      = (∑ i ∈ Finset.range 190, stT297 (i+1)) + stT297 191 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 190
    simpa using h
  have hprev := st297_p190
  have hstep := st297_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p192 : ((4569017639351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT297 (i+1))
      = (∑ i ∈ Finset.range 191, stT297 (i+1)) + stT297 192 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 191
    simpa using h
  have hprev := st297_p191
  have hstep := st297_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p193 : ((36882297941043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT297 (i+1))
      = (∑ i ∈ Finset.range 192, stT297 (i+1)) + stT297 193 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 192
    simpa using h
  have hprev := st297_p192
  have hstep := st297_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p194 : ((7506316508077/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT297 (i+1))
      = (∑ i ∈ Finset.range 193, stT297 (i+1)) + stT297 194 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 193
    simpa using h
  have hprev := st297_p193
  have hstep := st297_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p195 : ((745093661389/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT297 (i+1))
      = (∑ i ∈ Finset.range 194, stT297 (i+1)) + stT297 195 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 194
    simpa using h
  have hprev := st297_p194
  have hstep := st297_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p196 : ((9145621593/2500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT297 (i+1))
      = (∑ i ∈ Finset.range 195, stT297 (i+1)) + stT297 196 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 195
    simpa using h
  have hprev := st297_p195
  have hstep := st297_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p197 : ((1839169504377/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT297 (i+1))
      = (∑ i ∈ Finset.range 196, stT297 (i+1)) + stT297 197 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 196
    simpa using h
  have hprev := st297_p196
  have hstep := st297_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p198 : ((18738509333129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT297 (i+1))
      = (∑ i ∈ Finset.range 197, stT297 (i+1)) + stT297 198 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 197
    simpa using h
  have hprev := st297_p197
  have hstep := st297_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p199 : ((18687471246893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT297 (i+1))
      = (∑ i ∈ Finset.range 198, stT297 (i+1)) + stT297 199 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 198
    simpa using h
  have hprev := st297_p198
  have hstep := st297_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p200 : ((36669137277773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT297 (i+1))
      = (∑ i ∈ Finset.range 199, stT297 (i+1)) + stT297 200 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 199
    simpa using h
  have hprev := st297_p199
  have hstep := st297_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p201 : ((36649908135121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT297 (i+1))
      = (∑ i ∈ Finset.range 200, stT297 (i+1)) + stT297 201 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 200
    simpa using h
  have hprev := st297_p200
  have hstep := st297_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p202 : ((3734802903967/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT297 (i+1))
      = (∑ i ∈ Finset.range 201, stT297 (i+1)) + stT297 202 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 201
    simpa using h
  have hprev := st297_p201
  have hstep := st297_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p203 : ((293021179013/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT297 (i+1))
      = (∑ i ∈ Finset.range 202, stT297 (i+1)) + stT297 203 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 202
    simpa using h
  have hprev := st297_p202
  have hstep := st297_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p204 : ((36846463247703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT297 (i+1))
      = (∑ i ∈ Finset.range 203, stT297 (i+1)) + stT297 204 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 203
    simpa using h
  have hprev := st297_p203
  have hstep := st297_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p205 : ((4567199949841/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT297 (i+1))
      = (∑ i ∈ Finset.range 204, stT297 (i+1)) + stT297 205 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 204
    simpa using h
  have hprev := st297_p204
  have hstep := st297_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p206 : ((7423796157303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT297 (i+1))
      = (∑ i ∈ Finset.range 205, stT297 (i+1)) + stT297 206 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 205
    simpa using h
  have hprev := st297_p205
  have hstep := st297_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p207 : ((37575144959203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT297 (i+1))
      = (∑ i ∈ Finset.range 206, stT297 (i+1)) + stT297 207 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 206
    simpa using h
  have hprev := st297_p206
  have hstep := st297_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p208 : ((37120336066019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT297 (i+1))
      = (∑ i ∈ Finset.range 207, stT297 (i+1)) + stT297 208 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 207
    simpa using h
  have hprev := st297_p207
  have hstep := st297_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p209 : ((1141797624497/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT297 (i+1))
      = (∑ i ∈ Finset.range 208, stT297 (i+1)) + stT297 209 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 208
    simpa using h
  have hprev := st297_p208
  have hstep := st297_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p210 : ((36816210184479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT297 (i+1))
      = (∑ i ∈ Finset.range 209, stT297 (i+1)) + stT297 210 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 209
    simpa using h
  have hprev := st297_p209
  have hstep := st297_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p211 : ((37482139669011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT297 (i+1))
      = (∑ i ∈ Finset.range 210, stT297 (i+1)) + stT297 211 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 210
    simpa using h
  have hprev := st297_p210
  have hstep := st297_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p212 : ((37420740854417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT297 (i+1))
      = (∑ i ∈ Finset.range 211, stT297 (i+1)) + stT297 212 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 211
    simpa using h
  have hprev := st297_p211
  have hstep := st297_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p213 : ((4592235444073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT297 (i+1))
      = (∑ i ∈ Finset.range 212, stT297 (i+1)) + stT297 213 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 212
    simpa using h
  have hprev := st297_p212
  have hstep := st297_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p214 : ((146239322363/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT297 (i+1))
      = (∑ i ∈ Finset.range 213, stT297 (i+1)) + stT297 214 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 213
    simpa using h
  have hprev := st297_p213
  have hstep := st297_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p215 : ((9293496150397/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT297 (i+1))
      = (∑ i ∈ Finset.range 214, stT297 (i+1)) + stT297 215 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 214
    simpa using h
  have hprev := st297_p214
  have hstep := st297_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p216 : ((18790723602493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT297 (i+1))
      = (∑ i ∈ Finset.range 215, stT297 (i+1)) + stT297 216 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 215
    simpa using h
  have hprev := st297_p215
  have hstep := st297_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p217 : ((37128865995401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT297 (i+1))
      = (∑ i ∈ Finset.range 216, stT297 (i+1)) + stT297 217 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 216
    simpa using h
  have hprev := st297_p216
  have hstep := st297_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p218 : ((36542505640901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT297 (i+1))
      = (∑ i ∈ Finset.range 217, stT297 (i+1)) + stT297 218 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 217
    simpa using h
  have hprev := st297_p217
  have hstep := st297_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p219 : ((9187599876909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT297 (i+1))
      = (∑ i ∈ Finset.range 218, stT297 (i+1)) + stT297 219 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 218
    simpa using h
  have hprev := st297_p218
  have hstep := st297_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p220 : ((7484296876491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT297 (i+1))
      = (∑ i ∈ Finset.range 219, stT297 (i+1)) + stT297 220 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 219
    simpa using h
  have hprev := st297_p219
  have hstep := st297_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p221 : ((37507772728599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT297 (i+1))
      = (∑ i ∈ Finset.range 220, stT297 (i+1)) + stT297 221 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 220
    simpa using h
  have hprev := st297_p220
  have hstep := st297_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p222 : ((36879263729007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT297 (i+1))
      = (∑ i ∈ Finset.range 221, stT297 (i+1)) + stT297 222 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 221
    simpa using h
  have hprev := st297_p221
  have hstep := st297_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p223 : ((36504044771357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT297 (i+1))
      = (∑ i ∈ Finset.range 222, stT297 (i+1)) + stT297 223 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 222
    simpa using h
  have hprev := st297_p222
  have hstep := st297_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p224 : ((36951643138669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT297 (i+1))
      = (∑ i ∈ Finset.range 223, stT297 (i+1)) + stT297 224 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 223
    simpa using h
  have hprev := st297_p223
  have hstep := st297_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p225 : ((37540931216047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT297 (i+1))
      = (∑ i ∈ Finset.range 224, stT297 (i+1)) + stT297 225 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 224
    simpa using h
  have hprev := st297_p224
  have hstep := st297_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p226 : ((3738750690747/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT297 (i+1))
      = (∑ i ∈ Finset.range 225, stT297 (i+1)) + stT297 226 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 225
    simpa using h
  have hprev := st297_p225
  have hstep := st297_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p227 : ((18361978069717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT297 (i+1))
      = (∑ i ∈ Finset.range 226, stT297 (i+1)) + stT297 227 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 226
    simpa using h
  have hprev := st297_p226
  have hstep := st297_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p228 : ((4566640487923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT297 (i+1))
      = (∑ i ∈ Finset.range 227, stT297 (i+1)) + stT297 228 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 227
    simpa using h
  have hprev := st297_p227
  have hstep := st297_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p229 : ((9272953781189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT297 (i+1))
      = (∑ i ∈ Finset.range 228, stT297 (i+1)) + stT297 229 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 228
    simpa using h
  have hprev := st297_p228
  have hstep := st297_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p230 : ((9395673960199/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT297 (i+1))
      = (∑ i ∈ Finset.range 229, stT297 (i+1)) + stT297 230 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 229
    simpa using h
  have hprev := st297_p229
  have hstep := st297_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p231 : ((1864862727539/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT297 (i+1))
      = (∑ i ∈ Finset.range 230, stT297 (i+1)) + stT297 231 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 230
    simpa using h
  have hprev := st297_p230
  have hstep := st297_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p232 : ((36649120577449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT297 (i+1))
      = (∑ i ∈ Finset.range 231, stT297 (i+1)) + stT297 232 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 231
    simpa using h
  have hprev := st297_p231
  have hstep := st297_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p233 : ((36562431558799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT297 (i+1))
      = (∑ i ∈ Finset.range 232, stT297 (i+1)) + stT297 233 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 232
    simpa using h
  have hprev := st297_p232
  have hstep := st297_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p234 : ((37156179939719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT297 (i+1))
      = (∑ i ∈ Finset.range 233, stT297 (i+1)) + stT297 234 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 233
    simpa using h
  have hprev := st297_p233
  have hstep := st297_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p235 : ((37593904421951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT297 (i+1))
      = (∑ i ∈ Finset.range 234, stT297 (i+1)) + stT297 235 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 234
    simpa using h
  have hprev := st297_p234
  have hstep := st297_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p236 : ((37267333126791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT297 (i+1))
      = (∑ i ∈ Finset.range 235, stT297 (i+1)) + stT297 236 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 235
    simpa using h
  have hprev := st297_p235
  have hstep := st297_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p237 : ((36632028333561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT297 (i+1))
      = (∑ i ∈ Finset.range 236, stT297 (i+1)) + stT297 237 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 236
    simpa using h
  have hprev := st297_p236
  have hstep := st297_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p238 : ((36560910631701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT297 (i+1))
      = (∑ i ∈ Finset.range 237, stT297 (i+1)) + stT297 238 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 237
    simpa using h
  have hprev := st297_p237
  have hstep := st297_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p239 : ((37147358680143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT297 (i+1))
      = (∑ i ∈ Finset.range 238, stT297 (i+1)) + stT297 239 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 238
    simpa using h
  have hprev := st297_p238
  have hstep := st297_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p240 : ((9398702525019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT297 (i+1))
      = (∑ i ∈ Finset.range 239, stT297 (i+1)) + stT297 240 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 239
    simpa using h
  have hprev := st297_p239
  have hstep := st297_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p241 : ((18651828788823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT297 (i+1))
      = (∑ i ∈ Finset.range 240, stT297 (i+1)) + stT297 241 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 240
    simpa using h
  have hprev := st297_p240
  have hstep := st297_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p242 : ((36666019532571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT297 (i+1))
      = (∑ i ∈ Finset.range 241, stT297 (i+1)) + stT297 242 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 241
    simpa using h
  have hprev := st297_p241
  have hstep := st297_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p243 : ((4565889655693/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT297 (i+1))
      = (∑ i ∈ Finset.range 242, stT297 (i+1)) + stT297 243 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 242
    simpa using h
  have hprev := st297_p242
  have hstep := st297_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p244 : ((4633286306661/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT297 (i+1))
      = (∑ i ∈ Finset.range 243, stT297 (i+1)) + stT297 244 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 243
    simpa using h
  have hprev := st297_p243
  have hstep := st297_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p245 : ((4697070728187/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT297 (i+1))
      = (∑ i ∈ Finset.range 244, stT297 (i+1)) + stT297 245 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 244
    simpa using h
  have hprev := st297_p244
  have hstep := st297_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p246 : ((7479512834003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT297 (i+1))
      = (∑ i ∈ Finset.range 245, stT297 (i+1)) + stT297 246 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 245
    simpa using h
  have hprev := st297_p245
  have hstep := st297_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p247 : ((3676332482629/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT297 (i+1))
      = (∑ i ∈ Finset.range 246, stT297 (i+1)) + stT297 247 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 246
    simpa using h
  have hprev := st297_p246
  have hstep := st297_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p248 : ((36485771604199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT297 (i+1))
      = (∑ i ∈ Finset.range 247, stT297 (i+1)) + stT297 248 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 247
    simpa using h
  have hprev := st297_p247
  have hstep := st297_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p249 : ((36914379424567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT297 (i+1))
      = (∑ i ∈ Finset.range 248, stT297 (i+1)) + stT297 249 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 248
    simpa using h
  have hprev := st297_p248
  have hstep := st297_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_p250 : ((9376416507813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT297 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT297 (i+1))
      = (∑ i ∈ Finset.range 249, stT297 (i+1)) + stT297 250 := by
    have h := Finset.sum_range_succ (fun i => stT297 (i+1)) 249
    simpa using h
  have hprev := st297_p249
  have hstep := st297_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st297_s250 :
    |Real.sin (((297 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))
      - ((354629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 226573/2500000) (δ := 3757/250000000) (ψ := -19999/50000) 297 261
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 297`** (evaluated boundary). -/
theorem station_297_sign : hardyG ((((297:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 297 250 (by norm_num) (by norm_num)
    ((-19999/50000 : ℚ) : ℝ)
  have hchain := st297_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT297 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((297 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-19999/50000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st297_c250
  have hsinb := abs_le.mp st297_s250
  have hbdy_lo : ((-16731950222581/882092500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((297 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-19999/50000 : ℚ) : ℝ))) / 2
          - ((((297:ℕ)):ℝ))
            * Real.sin (((297 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-19999/50000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((297:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((297:ℝ) * Real.log (250:ℝ) - ((-19999/50000 : ℚ) : ℝ))) / 2
        - ((297:ℝ)) * Real.sin ((297:ℝ) * Real.log (250:ℝ) - ((-19999/50000 : ℚ) : ℝ))
        ≥ ((-211644133/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((297:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-211644133/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-211644133/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-211644133/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((297:ℕ)):ℝ))+1) * (((((297:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1801246783721/937500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((9376416507813/2500000000000 : ℚ) : ℝ) + ((-16731950222581/882092500000000 : ℚ) : ℝ)
      - ((1801246783721/937500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-19999/50000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((297:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-19999/50000 : ℚ) : ℝ)
        * (riemannZeta (line ((((297:ℕ)):ℝ)))).re
      - Real.sin ((-19999/50000 : ℚ) : ℝ)
        * (riemannZeta (line ((((297:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((297:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((297:ℕ)):ℝ))
      = (((((297:ℕ)):ℝ)) * (Real.log ((((297:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((297:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_297
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
  have hθwin : |(((-19999/50000 : ℚ) : ℝ) + ((68:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((297:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((297:ℕ)):ℝ)))
    (φ := ((-19999/50000 : ℚ) : ℝ) + ((68:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-19999/50000 : ℚ) : ℝ) + ((68:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-19999/50000 : ℚ)) : ℝ) - Real.pi) + ((68:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-19999/50000 : ℚ)) : ℝ) - Real.pi) 68).1,
    (cos_sin_shift ((((-19999/50000 : ℚ)) : ℝ) - Real.pi) 68).2]
  exact cos_sin_flip ((-19999/50000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_297_sign
end AxiomAudit
