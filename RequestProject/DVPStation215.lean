import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 215` (rung-217.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT215 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((215 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))

theorem st215_c1 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((72043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1782759/5000000) (δ := 201/1000000000) (ψ := -1426207/1000000) 215 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t1 : ((36009/250000 : ℚ) : ℝ) ≤ stT215 1 := by
  have hc : ((36009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36009/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((36009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c2 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((941547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6711/78125) (δ := 10829/1000000000) (ψ := -1426207/1000000) 215 24
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t2 : ((6657388367299/10000000000000 : ℚ) : ℝ) ≤ stT215 2 := by
  have hc : ((941497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6657388367299/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((941497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c3 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((423763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1416501/5000000) (δ := 5437/500000000) (ψ := -1426207/1000000) 215 38
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t3 : ((1223153926463/5000000000000 : ℚ) : ℝ) ≤ stT215 3 := by
  have hc : ((423713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1223153926463/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((423713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c4 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-516369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2641753/5000000) (δ := 5423/500000000) (ψ := -1426207/1000000) 215 48
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t4 : ((-2582095516419/10000000000000 : ℚ) : ℝ) ≤ stT215 4 := by
  have hc : ((-516419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2582095516419/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-516419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c5 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-152233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1175109/2500000) (δ := 2699/250000000) (ψ := -1426207/1000000) 215 55
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t5 : ((-42557405193/312500000000 : ℚ) : ℝ) ≤ stT215 5 := by
  have hc : ((-76129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42557405193/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-76129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c6 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-121459/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7257501/10000000) (δ := 1357/125000000) (ψ := -1426207/1000000) 215 62
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t6 : ((-1983519272863/5000000000000 : ℚ) : ℝ) ≤ stT215 6 := by
  have hc : ((-485861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1983519272863/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-485861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c7 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((192067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -735329/2500000) (δ := 541/50000000) (ψ := -1426207/1000000) 215 67
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t7 : ((90731299131/625000000000 : ℚ) : ℝ) ≤ stT215 7 := by
  have hc : ((96021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90731299131/625000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((96021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c8 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-737383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5999959/10000000) (δ := 10911/1000000000) (ψ := -1426207/1000000) 215 71
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t8 : ((-1303609722111/5000000000000 : ℚ) : ℝ) ≤ stT215 8 := by
  have hc : ((-737433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1303609722111/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-737433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c9 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-851999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619117/2500000) (δ := 10763/1000000000) (ψ := -1426207/1000000) 215 75
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t9 : ((-1420081950683/5000000000000 : ℚ) : ℝ) ≤ stT215 9 := by
  have hc : ((-852049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1420081950683/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-852049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c10 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((993917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68971/2500000) (δ := 10869/1000000000) (ψ := -1426207/1000000) 215 79
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t10 : ((3142882755159/10000000000000 : ℚ) : ℝ) ≤ stT215 10 := by
  have hc : ((993867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3142882755159/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((993867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c11 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-22587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2190613/5000000) (δ := 10913/1000000000) (ψ := -1426207/1000000) 215 82
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t11 : ((-136242448761/2500000000000 : ℚ) : ℝ) ≤ stT215 11 := by
  have hc : ((-90373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136242448761/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-90373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c12 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-39579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1006491/2500000) (δ := 10791/1000000000) (ψ := -1426207/1000000) 215 85
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t12 : ((-3574971719/312500000000 : ℚ) : ℝ) ≤ stT215 12 := by
  have hc : ((-39629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3574971719/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-39629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c13 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((19991/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37487/5000000) (δ := 10933/1000000000) (ψ := -1426207/1000000) 215 88
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t13 : ((11088453/40000000 : ℚ) : ℝ) ≤ stT215 13 := by
  have hc : ((1999/2000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11088453/40000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((1999/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c14 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-245249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3682907/5000000) (δ := 2171/200000000) (ψ := -1426207/1000000) 215 91
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t14 : ((-1310978146599/5000000000000 : ℚ) : ℝ) ≤ stT215 14 := by
  have hc : ((-490523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1310978146599/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-490523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c15 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((778061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1698057/10000000) (δ := 10769/1000000000) (ψ := -1426207/1000000) 215 93
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t15 : ((502203766467/2500000000000 : ℚ) : ℝ) ≤ stT215 15 := by
  have hc : ((778011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502203766467/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((778011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c16 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((807919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78773/500000) (δ := 10819/1000000000) (ψ := -1426207/1000000) 215 95
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t16 : ((807869/4000000 : ℚ) : ℝ) ≤ stT215 16 := by
  have hc : ((807869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((807869/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((807869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c17 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((227643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343157/1250000) (δ := 2161/200000000) (ψ := -1426207/1000000) 215 97
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t17 : ((69006835251/625000000000 : ℚ) : ℝ) ≤ stT215 17 := by
  have hc : ((113809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69006835251/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((113809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c18 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((136329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205197/1000000) (δ := 341/31250000) (ψ := -1426207/1000000) 215 99
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t18 : ((160653441009/1000000000000 : ℚ) : ℝ) ≤ stT215 18 := by
  have hc : ((136319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160653441009/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((136319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c19 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((31021/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302837/10000000) (δ := 1347/125000000) (ψ := -1426207/1000000) 215 101
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t19 : ((1138615354827/5000000000000 : ℚ) : ℝ) ≤ stT215 19 := by
  have hc : ((496311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1138615354827/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((496311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c20 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-44267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -829723/2000000) (δ := 5431/500000000) (ψ := -1426207/1000000) 215 103
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t20 : ((-6189995241/312500000000 : ℚ) : ℝ) ≤ stT215 20 := by
  have hc : ((-11073/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6189995241/312500000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-11073/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c21 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-828523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1273631/2000000) (δ := 2737/250000000) (ψ := -1426207/1000000) 215 104
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t21 : ((-1808094600567/10000000000000 : ℚ) : ℝ) ≤ stT215 21 := by
  have hc : ((-828573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1808094600567/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-828573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c22 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((19997/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5409/1250000) (δ := 10763/1000000000) (ψ := -1426207/1000000) 215 106
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t22 : ((10657902993/50000000000 : ℚ) : ℝ) ≤ stT215 22 := by
  have hc : ((4999/5000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10657902993/50000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((4999/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c23 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-993389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1891589/2500000) (δ := 10777/1000000000) (ψ := -1426207/1000000) 215 108
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t23 : ((-414292872731/2000000000000 : ℚ) : ℝ) ≤ stT215 23 := by
  have hc : ((-993439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-414292872731/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-993439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c24 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((987321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199267/5000000) (δ := 2721/250000000) (ψ := -1426207/1000000) 215 109
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t24 : ((2015258043311/10000000000000 : ℚ) : ℝ) ≤ stT215 24 := by
  have hc : ((987271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2015258043311/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((987271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c25 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-138267/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5835327/10000000) (δ := 341/31250000) (ψ := -1426207/1000000) 215 110
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t25 : ((-276554138277/2000000000000 : ℚ) : ℝ) ≤ stT215 25 := by
  have hc : ((-138277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276554138277/2000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-138277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c26 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-226997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4499473/10000000) (δ := 10797/1000000000) (ψ := -1426207/1000000) 215 112
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t26 : ((-222637974307/5000000000000 : ℚ) : ℝ) ≤ stT215 26 := by
  have hc : ((-227047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222637974307/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-227047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c27 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((499757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3119/400000) (δ := 1079/100000000) (ψ := -1426207/1000000) 215 113
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t27 : ((480867117/2500000000 : ℚ) : ℝ) ≤ stT215 27 := by
  have hc : ((124933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480867117/2500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((124933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c28 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((467/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3917651/10000000) (δ := 273/25000000) (ψ := -1426207/1000000) 215 114
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t28 : ((1741470973/2500000000000 : ℚ) : ℝ) ≤ stT215 28 := by
  have hc : ((1843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1741470973/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((1843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c29 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-951387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7071261/10000000) (δ := 1347/125000000) (ψ := -1426207/1000000) 215 115
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t29 : ((-883387371449/5000000000000 : ℚ) : ℝ) ≤ stT215 29 := by
  have hc : ((-951437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-883387371449/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-951437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c30 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-769621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6122609/10000000) (δ := 5421/500000000) (ψ := -1426207/1000000) 215 117
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t30 : ((-702610335441/5000000000000 : ℚ) : ℝ) ≤ stT215 30 := by
  have hc : ((-769671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-702610335441/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-769671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c31 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-111373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4206001/10000000) (δ := 10849/1000000000) (ψ := -1426207/1000000) 215 118
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t31 : ((-100060862421/5000000000000 : ℚ) : ℝ) ≤ stT215 31 := by
  have hc : ((-111423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100060862421/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-111423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c32 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((52243/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1424519/5000000) (δ := 1357/125000000) (ψ := -1426207/1000000) 215 119
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t32 : ((184684701201/2500000000000 : ℚ) : ℝ) ≤ stT215 32 := by
  have hc : ((208947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184684701201/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((208947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c33 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((138347/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2017267/10000000) (δ := 547/50000000) (ψ := -1426207/1000000) 215 120
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t33 : ((30101716189/250000000000 : ℚ) : ℝ) ≤ stT215 33 := by
  have hc : ((138337/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30101716189/250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((138337/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c34 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((782767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -839621/5000000) (δ := 1087/100000000) (ψ := -1426207/1000000) 215 121
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t34 : ((268469582849/2000000000000 : ℚ) : ℝ) ≤ stT215 34 := by
  have hc : ((782717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268469582849/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((782717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c35 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((750109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225803/1250000) (δ := 10877/1000000000) (ψ := -1426207/1000000) 215 122
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t35 : ((316957682043/2500000000000 : ℚ) : ℝ) ≤ stT215 35 := by
  have hc : ((750059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316957682043/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((750059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c36 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((582487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2372529/10000000) (δ := 5409/500000000) (ψ := -1426207/1000000) 215 123
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t36 : ((485363972521/5000000000000 : ℚ) : ℝ) ≤ stT215 36 := by
  have hc : ((582437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((485363972521/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((582437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c37 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((113689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335353/1000000) (δ := 10911/1000000000) (ψ := -1426207/1000000) 215 124
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t37 : ((182482779/4882812500 : ℚ) : ℝ) ≤ stT215 37 := by
  have hc : ((3552/15625 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182482779/4882812500 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((3552/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c38 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-314697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945467/2000000) (δ := 10899/1000000000) (ψ := -1426207/1000000) 215 125
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t38 : ((-102117460921/2000000000000 : ℚ) : ℝ) ≤ stT215 38 := by
  have hc : ((-314747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102117460921/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-314747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c39 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-851369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6473467/10000000) (δ := 5453/500000000) (ψ := -1426207/1000000) 215 126
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t39 : ((-681680959579/5000000000000 : ℚ) : ℝ) ≤ stT215 39 := by
  have hc : ((-851419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-681680959579/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-851419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c40 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-14983/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142697/200000) (δ := 10797/1000000000) (ψ := -1426207/1000000) 215 126
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t40 : ((-758126108859/5000000000000 : ℚ) : ℝ) ≤ stT215 40 := by
  have hc : ((-479481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-758126108859/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-479481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c41 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-15199/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4699159/10000000) (δ := 1089/100000000) (ψ := -1426207/1000000) 215 127
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t41 : ((-23740760207/500000000000 : ℚ) : ℝ) ≤ stT215 41 := by
  have hc : ((-30403/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23740760207/500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-30403/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c42 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((89087/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242957/1250000) (δ := 10783/1000000000) (ψ := -1426207/1000000) 215 128
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t42 : ((549818147659/5000000000000 : ℚ) : ℝ) ≤ stT215 42 := by
  have hc : ((356323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((549818147659/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((356323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c43 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((901893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1116663/10000000) (δ := 683/62500000) (ψ := -1426207/1000000) 215 129
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t43 : ((275059409471/2000000000000 : ℚ) : ℝ) ≤ stT215 43 := by
  have hc : ((901843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275059409471/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((901843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c44 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-214629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -446777/1000000) (δ := 2187/200000000) (ψ := -1426207/1000000) 215 130
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t44 : ((-323640829203/10000000000000 : ℚ) : ℝ) ≤ stT215 44 := by
  have hc : ((-214679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323640829203/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-214679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c45 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-497647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47571/62500) (δ := 2187/200000000) (ψ := -1426207/1000000) 215 130
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t45 : ((-11591962851/78125000000 : ℚ) : ℝ) ≤ stT215 45 := by
  have hc : ((-62209/62500 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11591962851/78125000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-62209/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c46 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((20969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 743411/2000000) (δ := 10761/1000000000) (ψ := -1426207/1000000) 215 131
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t46 : ((61797323547/5000000000000 : ℚ) : ℝ) ≤ stT215 46 := by
  have hc : ((41913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61797323547/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((41913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c47 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((985157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53909/1250000) (δ := 5377/500000000) (ψ := -1426207/1000000) 215 132
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t47 : ((1436925340443/10000000000000 : ℚ) : ℝ) ≤ stT215 47 := by
  have hc : ((985107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1436925340443/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((985107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c48 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-43849/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4823033/10000000) (δ := 10847/1000000000) (ψ := -1426207/1000000) 215 133
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t48 : ((-15824903831/312500000000 : ℚ) : ℝ) ≤ stT215 48 := by
  have hc : ((-175421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15824903831/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-175421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c49 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-20087/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6259787/10000000) (δ := 10847/1000000000) (ψ := -1426207/1000000) 215 133
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t49 : ((-28697511479/250000000000 : ℚ) : ℝ) ≤ stT215 49 := by
  have hc : ((-80353/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28697511479/250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-80353/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c50 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((422473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1410829/10000000) (δ := 2691/250000000) (ψ := -1426207/1000000) 215 134
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t50 : ((37339465839/312500000000 : ℚ) : ℝ) ≤ stT215 50 := by
  have hc : ((26403/31250 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37339465839/312500000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((26403/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c51 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((109283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3653237/10000000) (δ := 677/62500000) (ψ := -1426207/1000000) 215 135
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t51 : ((3823919631/250000000000 : ℚ) : ℝ) ≤ stT215 51 := by
  have hc : ((109233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3823919631/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((109233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c52 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-909799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847999/1250000) (δ := 10771/1000000000) (ψ := -1426207/1000000) 215 135
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t52 : ((-1261734010599/10000000000000 : ℚ) : ℝ) ≤ stT215 52 := by
  have hc : ((-909849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1261734010599/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-909849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c53 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((108117/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328609/2500000) (δ := 433/40000000) (ψ := -1426207/1000000) 215 136
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t53 : ((118801173403/1000000000000 : ℚ) : ℝ) ≤ stT215 53 := by
  have hc : ((432443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118801173403/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((432443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c54 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-83513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4346523/10000000) (δ := 2177/200000000) (ψ := -1426207/1000000) 215 137
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t54 : ((-14210106183/625000000000 : ℚ) : ℝ) ≤ stT215 54 := by
  have hc : ((-41769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14210106183/625000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-41769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c55 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-593701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2758059/5000000) (δ := 2157/200000000) (ψ := -1426207/1000000) 215 137
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t55 : ((-2001534621/25000000000 : ℚ) : ℝ) ≤ stT215 55 := by
  have hc : ((-593751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2001534621/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-593751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c56 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((489757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253451/5000000) (δ := 10911/1000000000) (ψ := -1426207/1000000) 215 138
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t56 : ((81803976249/625000000000 : ℚ) : ℝ) ≤ stT215 56 := by
  have hc : ((122433/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81803976249/625000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((122433/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c57 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-895581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670133/1000000) (δ := 2701/250000000) (ψ := -1426207/1000000) 215 139
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t57 : ((-1186292815323/10000000000000 : ℚ) : ℝ) ≤ stT215 57 := by
  have hc : ((-895631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1186292815323/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-895631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c58 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((490001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2646763/10000000) (δ := 10899/1000000000) (ψ := -1426207/1000000) 215 139
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t58 : ((80417127483/1250000000000 : ℚ) : ℝ) ≤ stT215 58 := by
  have hc : ((489951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80417127483/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((489951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c59 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((2161/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3872961/10000000) (δ := 681/62500000) (ψ := -1426207/1000000) 215 140
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t59 : ((701718171/250000000000 : ℚ) : ℝ) ≤ stT215 59 := by
  have hc : ((539/25000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((701718171/250000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((539/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c60 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-59219/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645107/1250000) (δ := 10907/1000000000) (ψ := -1426207/1000000) 215 140
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t60 : ((-61167601299/1000000000000 : ℚ) : ℝ) ≤ stT215 60 := by
  have hc : ((-236901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61167601299/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-236901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c61 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((78689/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1662609/10000000) (δ := 10789/1000000000) (ψ := -1426207/1000000) 215 141
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t61 : ((1574132433/15625000000 : ℚ) : ℝ) ≤ stT215 61 := by
  have hc : ((19671/25000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1574132433/15625000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((19671/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c62 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-476071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707741/1000000) (δ := 5407/500000000) (ψ := -1426207/1000000) 215 141
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t62 : ((-4723772439/39062500000 : ℚ) : ℝ) ≤ stT215 62 := by
  have hc : ((-14878/15625 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4723772439/39062500000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-14878/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c63 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((499963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15169/5000000) (δ := 10921/1000000000) (ψ := -1426207/1000000) 215 142
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t63 : ((314931193689/2500000000000 : ℚ) : ℝ) ≤ stT215 63 := by
  have hc : ((249969/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((314931193689/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((249969/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c64 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-243293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727359/1000000) (δ := 683/62500000) (ψ := -1426207/1000000) 215 143
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t64 : ((-608264236611/5000000000000 : ℚ) : ℝ) ≤ stT215 64 := by
  have hc : ((-486611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608264236611/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-486611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c65 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((113933/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1059917/10000000) (δ := 431/40000000) (ψ := -1426207/1000000) 215 143
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t65 : ((565234810329/5000000000000 : ℚ) : ℝ) ≤ stT215 65 := by
  have hc : ((455707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565234810329/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((455707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c66 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-844649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1288353/2000000) (δ := 673/62500000) (ψ := -1426207/1000000) 215 144
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t66 : ((-207950533917/2000000000000 : ℚ) : ℝ) ≤ stT215 66 := by
  have hc : ((-844699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207950533917/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-844699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c67 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((99021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820553/5000000) (δ := 2717/250000000) (ψ := -1426207/1000000) 215 144
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t67 : ((241931451973/2500000000000 : ℚ) : ℝ) ≤ stT215 67 := by
  have hc : ((396059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241931451973/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((396059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c68 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-38239/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6103741/10000000) (δ := 543/50000000) (ψ := -1426207/1000000) 215 145
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t68 : ((-92749327957/1000000000000 : ℚ) : ℝ) ≤ stT215 68 := by
  have hc : ((-76483/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92749327957/1000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-76483/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c69 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((383307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 871557/5000000) (δ := 543/50000000) (ψ := -1426207/1000000) 215 145
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t69 : ((115354275489/1250000000000 : ℚ) : ℝ) ≤ stT215 69 := by
  have hc : ((191641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115354275489/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((191641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c70 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-398277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6230923/10000000) (δ := 10853/1000000000) (ψ := -1426207/1000000) 215 146
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t70 : ((-238031050579/2500000000000 : ℚ) : ℝ) ≤ stT215 70 := by
  have hc : ((-199151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238031050579/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-199151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c71 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((212169/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13933/100000) (δ := 217/20000000) (ψ := -1426207/1000000) 215 146
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t71 : ((503566606453/5000000000000 : ℚ) : ℝ) ≤ stT215 71 := by
  have hc : ((424313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((503566606453/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((424313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c72 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-911951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6797027/10000000) (δ := 10857/1000000000) (ψ := -1426207/1000000) 215 147
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t72 : ((-67175257657/625000000000 : ℚ) : ℝ) ≤ stT215 72 := by
  have hc : ((-912001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67175257657/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-912001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c73 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((60607/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 616871/10000000) (δ := 5473/500000000) (ψ := -1426207/1000000) 215 147
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t73 : ((567451535541/5000000000000 : ℚ) : ℝ) ≤ stT215 73 := by
  have hc : ((484831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567451535541/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((484831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c74 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-999539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3889041/5000000) (δ := 10839/1000000000) (ψ := -1426207/1000000) 215 148
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t74 : ((-1161999221953/10000000000000 : ℚ) : ℝ) ≤ stT215 74 := by
  have hc : ((-999589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1161999221953/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-999589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c75 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((194947/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281583/5000000) (δ := 10939/1000000000) (ψ := -1426207/1000000) 215 148
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t75 : ((2250937539/20000000000 : ℚ) : ℝ) ≤ stT215 75 := by
  have hc : ((194937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2250937539/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((194937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c76 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-434123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6556129/10000000) (δ := 10939/1000000000) (ψ := -1426207/1000000) 215 148
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t76 : ((-124500513423/1250000000000 : ℚ) : ℝ) ≤ stT215 76 := by
  have hc : ((-108537/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124500513423/1250000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-108537/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c77 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((659809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106279/500000) (δ := 10771/1000000000) (ψ := -1426207/1000000) 215 149
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t77 : ((150372931039/2000000000000 : ℚ) : ℝ) ≤ stT215 77 := by
  have hc : ((659759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150372931039/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((659759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c78 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-21619/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4809997/10000000) (δ := 2733/250000000) (ψ := -1426207/1000000) 215 149
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t78 : ((-97929025803/2500000000000 : ℚ) : ℝ) ≤ stT215 78 := by
  have hc : ((-172977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97929025803/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-172977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c79 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-9897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4050753/10000000) (δ := 5439/500000000) (ψ := -1426207/1000000) 215 150
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t79 : ((-348320213/62500000000 : ℚ) : ℝ) ≤ stT215 79 := by
  have hc : ((-9907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348320213/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-9907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c80 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((58459/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169397/625000) (δ := 5439/500000000) (ψ := -1426207/1000000) 215 150
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t80 : ((261408413763/5000000000000 : ℚ) : ℝ) ≤ stT215 80 := by
  have hc : ((233811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261408413763/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((233811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c81 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-102213/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3160259/5000000) (δ := 10817/1000000000) (ψ := -1426207/1000000) 215 151
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t81 : ((-56788517653/625000000000 : ℚ) : ℝ) ≤ stT215 81 := by
  have hc : ((-408877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56788517653/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-408877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c82 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((993971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274661/10000000) (δ := 5393/500000000) (ψ := -1426207/1000000) 215 151
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t82 : ((219520373823/2000000000000 : ℚ) : ℝ) ≤ stT215 82 := by
  have hc : ((993921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219520373823/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((993921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c83 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-45539/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6789913/10000000) (δ := 10917/1000000000) (ψ := -1426207/1000000) 215 151
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t83 : ((-99976617369/1000000000000 : ℚ) : ℝ) ≤ stT215 83 := by
  have hc : ((-91083/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99976617369/1000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-91083/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c84 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((273363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2480869/10000000) (δ := 21593/1000000000) (ψ := -1426207/1000000) 215 152
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t84 : ((149118042541/2500000000000 : ℚ) : ℝ) ≤ stT215 84 := by
  have hc : ((136669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149118042541/2500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((136669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c85 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((1171/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970037/2500000) (δ := 10893/1000000000) (ψ := -1426207/1000000) 215 152
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t85 : ((2533475909/1250000000000 : ℚ) : ℝ) ≤ stT215 85 := by
  have hc : ((9343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2533475909/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((9343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c86 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-2407/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173163/312500) (δ := 10903/1000000000) (ψ := -1426207/1000000) 215 153
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t86 : ((-405586119/6250000000 : ℚ) : ℝ) ≤ stT215 86 := by
  have hc : ((-3009/5000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405586119/6250000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-3009/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c87 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((964009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5256/78125) (δ := 10803/1000000000) (ψ := -1426207/1000000) 215 153
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t87 : ((64592000713/625000000000 : ℚ) : ℝ) ≤ stT215 87 := by
  have hc : ((963959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64592000713/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((963959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c88 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-914989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3407847/5000000) (δ := 10903/1000000000) (ψ := -1426207/1000000) 215 153
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t88 : ((-243858808539/2500000000000 : ℚ) : ℝ) ≤ stT215 88 := by
  have hc : ((-915039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243858808539/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-915039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c89 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((214453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -704697/2500000) (δ := 681/62500000) (ψ := -1426207/1000000) 215 154
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t89 : ((56823259179/1250000000000 : ℚ) : ℝ) ≤ stT215 89 := by
  have hc : ((53607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56823259179/1250000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((53607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c90 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((145873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3186861/10000000) (δ := 2699/250000000) (ψ := -1426207/1000000) 215 154
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t90 : ((4804287813/156250000000 : ℚ) : ℝ) ≤ stT215 90 := by
  have hc : ((18231/62500 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4804287813/156250000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((18231/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c91 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-54581/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -411363/625000) (δ := 21589/1000000000) (ψ := -1426207/1000000) 215 155
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t91 : ((-91551551161/1000000000000 : ℚ) : ℝ) ≤ stT215 91 := by
  have hc : ((-436673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91551551161/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-436673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c92 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((240057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -707443/10000000) (δ := 5457/500000000) (ψ := -1426207/1000000) 215 155
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t92 : ((125131837227/1250000000000 : ℚ) : ℝ) ≤ stT215 92 := by
  have hc : ((480089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125131837227/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((480089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c93 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-226697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1020683/2000000) (δ := 10889/1000000000) (ψ := -1426207/1000000) 215 155
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t93 : ((-14693739459/312500000000 : ℚ) : ℝ) ≤ stT215 93 := by
  have hc : ((-113361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14693739459/312500000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-113361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c94 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-72609/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303489/625000) (δ := 5411/500000000) (ψ := -1426207/1000000) 215 156
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t94 : ((-37450417109/1000000000000 : ℚ) : ℝ) ≤ stT215 94 := by
  have hc : ((-72619/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37450417109/1000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-72619/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c95 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((236281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166411/2000000) (δ := 5461/500000000) (ψ := -1426207/1000000) 215 156
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t95 : ((242406283093/2500000000000 : ℚ) : ℝ) ≤ stT215 95 := by
  have hc : ((472537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242406283093/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((472537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c96 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-848611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3230189/5000000) (δ := 10881/1000000000) (ψ := -1426207/1000000) 215 156
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t96 : ((-866161238481/10000000000000 : ℚ) : ℝ) ≤ stT215 96 := by
  have hc : ((-848661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866161238481/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-848661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c97 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((99599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183879/500000) (δ := 5387/500000000) (ψ := -1426207/1000000) 215 157
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t97 : ((50538339477/5000000000000 : ℚ) : ℝ) ≤ stT215 97 := by
  have hc : ((99549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50538339477/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((99549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c98 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((92803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1835289/10000000) (δ := 10829/1000000000) (ψ := -1426207/1000000) 215 157
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t98 : ((46869411303/625000000000 : ℚ) : ℝ) ≤ stT215 98 := by
  have hc : ((371187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46869411303/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((371187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c99 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-974859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1823051/2500000) (δ := 10829/1000000000) (ψ := -1426207/1000000) 215 157
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t99 : ((-489910295771/5000000000000 : ℚ) : ℝ) ≤ stT215 99 := by
  have hc : ((-974909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489910295771/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-974909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c100 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((89309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3013723/10000000) (δ := 2709/250000000) (ψ := -1426207/1000000) 215 158
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t100 : ((178592821407/5000000000000 : ℚ) : ℝ) ≤ stT215 100 := by
  have hc : ((178593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178592821407/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((178593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c101 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((297373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2334617/10000000) (δ := 2709/250000000) (ψ := -1426207/1000000) 215 158
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t101 : ((73968065469/1250000000000 : ℚ) : ℝ) ≤ stT215 101 := by
  have hc : ((74337/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73968065469/1250000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((74337/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c102 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-995997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1907557/2500000) (δ := 10767/1000000000) (ψ := -1426207/1000000) 215 158
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t102 : ((-246558486239/2500000000000 : ℚ) : ℝ) ≤ stT215 102 := by
  have hc : ((-996047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246558486239/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-996047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c103 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((211731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2833831/10000000) (δ := 10943/1000000000) (ψ := -1426207/1000000) 215 159
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t103 : ((104300030637/2500000000000 : ℚ) : ℝ) ≤ stT215 103 := by
  have hc : ((105853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104300030637/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((105853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c104 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((293367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29493/125000) (δ := 10843/1000000000) (ψ := -1426207/1000000) 215 159
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t104 : ((7191132459/125000000000 : ℚ) : ℝ) ≤ stT215 104 := by
  have hc : ((146671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7191132459/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((146671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c105 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-247541/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3751523/5000000) (δ := 269/25000000) (ψ := -1426207/1000000) 215 159
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t105 : ((-483175416407/5000000000000 : ℚ) : ℝ) ≤ stT215 105 := by
  have hc : ((-495107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483175416407/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-495107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c106 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((320967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -777529/2500000) (δ := 10753/1000000000) (ψ := -1426207/1000000) 215 160
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t106 : ((62340373669/2000000000000 : ℚ) : ℝ) ≤ stT215 106 := by
  have hc : ((320917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62340373669/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((320917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c107 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((178647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 968451/5000000) (δ := 219/20000000) (ψ := -1426207/1000000) 215 160
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t107 : ((21586550249/312500000000 : ℚ) : ℝ) ≤ stT215 107 := by
  have hc : ((357269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21586550249/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((357269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c108 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-466737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3468471/5000000) (δ := 219/20000000) (ψ := -1426207/1000000) 215 160
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t108 : ((-224571100631/2500000000000 : ℚ) : ℝ) ≤ stT215 108 := by
  have hc : ((-233381/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224571100631/2500000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-233381/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c109 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((43943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3817099/10000000) (δ := 10857/1000000000) (ψ := -1426207/1000000) 215 161
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t109 : ((21020928309/5000000000000 : ℚ) : ℝ) ≤ stT215 109 := by
  have hc : ((43893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21020928309/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((43893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c110 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((453087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1091619/10000000) (δ := 5473/500000000) (ψ := -1426207/1000000) 215 161
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t110 : ((107994350161/1250000000000 : ℚ) : ℝ) ≤ stT215 110 := by
  have hc : ((226531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107994350161/1250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((226531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c111 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-11334/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5955941/10000000) (δ := 10857/1000000000) (ψ := -1426207/1000000) 215 161
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t111 : ((-172135972827/2500000000000 : ℚ) : ℝ) ≤ stT215 111 := by
  have hc : ((-362713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172135972827/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-362713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c112 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-195521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24657/50000) (δ := 2153/200000000) (ψ := -1426207/1000000) 215 162
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t112 : ((-5774180061/156250000000 : ℚ) : ℝ) ≤ stT215 112 := by
  have hc : ((-97773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5774180061/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-97773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c113 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((499057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153563/10000000) (δ := 5469/500000000) (ψ := -1426207/1000000) 215 162
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t113 : ((733514661/7812500000 : ℚ) : ℝ) ≤ stT215 113 := by
  have hc : ((62379/62500 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((733514661/7812500000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((62379/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c114 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-259069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 916427/2000000) (δ := 2153/200000000) (ψ := -1426207/1000000) 215 162
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t114 : ((-121343613867/5000000000000 : ℚ) : ℝ) ≤ stT215 114 := by
  have hc : ((-259119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121343613867/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-259119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c115 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-842437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1286293/2000000) (δ := 10931/1000000000) (ψ := -1426207/1000000) 215 163
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t115 : ((-157124667987/2000000000000 : ℚ) : ℝ) ≤ stT215 115 := by
  have hc : ((-842487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157124667987/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-842487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c116 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((378817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177779/1000000) (δ := 10931/1000000000) (ψ := -1426207/1000000) 215 163
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t116 : ((10990602531/156250000000 : ℚ) : ℝ) ≤ stT215 116 := by
  have hc : ((47349/62500 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10990602531/156250000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((47349/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c117 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((16907/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2836003/10000000) (δ := 2693/250000000) (ψ := -1426207/1000000) 215 163
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t117 : ((6251469/160000000 : ℚ) : ℝ) ≤ stT215 117 := by
  have hc : ((3381/8000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6251469/160000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((3381/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c118 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-984307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926313/1250000) (δ := 10831/1000000000) (ψ := -1426207/1000000) 215 163
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t118 : ((-36246977811/400000000000 : ℚ) : ℝ) ≤ stT215 118 := by
  have hc : ((-984357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36246977811/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-984357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c119 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((33053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -940401/2500000) (δ := 10779/1000000000) (ψ := -1426207/1000000) 215 164
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t119 : ((3784587693/625000000000 : ℚ) : ℝ) ≤ stT215 119 := by
  have hc : ((8257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3784587693/625000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((8257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c120 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((191387/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736357/10000000) (δ := 1353/125000000) (ψ := -1426207/1000000) 215 164
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t120 : ((17470232199/200000000000 : ℚ) : ℝ) ≤ stT215 120 := by
  have hc : ((191377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17470232199/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((191377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c121 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-486421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2598481/5000000) (δ := 1353/125000000) (ψ := -1426207/1000000) 215 164
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t121 : ((-442246407861/10000000000000 : ℚ) : ℝ) ≤ stT215 121 := by
  have hc : ((-486471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-442246407861/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-486471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c122 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-190119/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6087107/10000000) (δ := 5443/500000000) (ψ := -1426207/1000000) 215 165
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t122 : ((-172137074577/2500000000000 : ℚ) : ℝ) ≤ stT215 122 := by
  have hc : ((-380263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172137074577/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-380263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c123 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((38887/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -849667/5000000) (δ := 10917/1000000000) (ψ := -1426207/1000000) 215 165
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t123 : ((70121896461/1000000000000 : ℚ) : ℝ) ≤ stT215 123 := by
  have hc : ((77769/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70121896461/1000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((77769/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c124 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((30491/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2652911/10000000) (δ := 10917/1000000000) (ψ := -1426207/1000000) 215 165
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t124 : ((109515617739/2500000000000 : ℚ) : ℝ) ≤ stT215 124 := by
  have hc : ((243903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109515617739/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((243903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c125 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-187633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6970219/10000000) (δ := 5393/500000000) (ψ := -1426207/1000000) 215 165
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t125 : ((-41958288301/500000000000 : ℚ) : ℝ) ≤ stT215 125 := by
  have hc : ((-187643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41958288301/500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-187643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c126 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-209573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4454837/10000000) (δ := 1081/100000000) (ψ := -1426207/1000000) 215 166
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t126 : ((-186747051633/10000000000000 : ℚ) : ℝ) ≤ stT215 126 := by
  have hc : ((-209623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186747051633/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-209623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c127 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((249153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102923/5000000) (δ := 1091/100000000) (ψ := -1426207/1000000) 215 166
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t127 : ((110538158759/1250000000000 : ℚ) : ℝ) ≤ stT215 127 := by
  have hc : ((498281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110538158759/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((498281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c128 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-33147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2004937/5000000) (δ := 1091/100000000) (ψ := -1426207/1000000) 215 166
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t128 : ((-7335574287/2500000000000 : ℚ) : ℝ) ≤ stT215 128 := by
  have hc : ((-33197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7335574287/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-33197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c129 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-99083/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1878789/2500000) (δ := 109/10000000) (ψ := -1426207/1000000) 215 167
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t129 : ((-5452633043/62500000000 : ℚ) : ℝ) ≤ stT215 129 := by
  have hc : ((-6193/6250 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5452633043/62500000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-6193/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c130 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((223071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3364581/10000000) (δ := 109/10000000) (ψ := -1426207/1000000) 215 167
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t130 : ((97801176109/5000000000000 : ℚ) : ℝ) ≤ stT215 130 := by
  have hc : ((223021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97801176109/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((223021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c131 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((190967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 754227/10000000) (δ := 10903/1000000000) (ψ := -1426207/1000000) 215 167
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t131 : ((20854986841/250000000000 : ℚ) : ℝ) ≤ stT215 131 := by
  have hc : ((190957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20854986841/250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((190957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c132 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-14311/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48417/100000) (δ := 27/2500000) (ψ := -1426207/1000000) 215 167
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t132 : ((-12457877757/400000000000 : ℚ) : ℝ) ≤ stT215 132 := by
  have hc : ((-14313/40000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12457877757/400000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-14313/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c133 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-91401/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6809643/10000000) (δ := 2727/250000000) (ψ := -1426207/1000000) 215 168
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t133 : ((-3962952833/50000000000 : ℚ) : ℝ) ≤ stT215 133 := by
  have hc : ((-45703/50000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3962952833/50000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-45703/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c134 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((441643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2783419/10000000) (δ := 5377/250000000) (ψ := -1426207/1000000) 215 168
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t134 : ((95369515431/2500000000000 : ℚ) : ℝ) ≤ stT215 134 := by
  have hc : ((441593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95369515431/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((441593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c135 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((884607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1212867/10000000) (δ := 2727/250000000) (ψ := -1426207/1000000) 215 168
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t135 : ((380652298367/5000000000000 : ℚ) : ℝ) ≤ stT215 135 := by
  have hc : ((884557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380652298367/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((884557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c136 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-240183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 517967/1000000) (δ := 2179/200000000) (ψ := -1426207/1000000) 215 168
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t136 : ((-12873542409/312500000000 : ℚ) : ℝ) ≤ stT215 136 := by
  have hc : ((-15013/31250 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12873542409/312500000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-15013/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c137 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-874987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3295257/5000000) (δ := 2163/200000000) (ψ := -1426207/1000000) 215 169
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t137 : ((-373797430623/5000000000000 : ℚ) : ℝ) ≤ stT215 137 := by
  have hc : ((-875037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373797430623/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-875037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c138 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((59733/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1340719/5000000) (δ := 2697/250000000) (ψ := -1426207/1000000) 215 169
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t138 : ((25421377149/625000000000 : ℚ) : ℝ) ≤ stT215 138 := by
  have hc : ((238907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25421377149/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((238907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c139 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((221773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1199473/10000000) (δ := 1361/125000000) (ψ := -1426207/1000000) 215 169
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t139 : ((94047297487/1250000000000 : ℚ) : ℝ) ≤ stT215 139 := by
  have hc : ((443521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94047297487/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((443521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c140 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-108791/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2526271/5000000) (δ := 2697/250000000) (ψ := -1426207/1000000) 215 169
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t140 : ((-36782328817/1000000000000 : ℚ) : ℝ) ≤ stT215 140 := by
  have hc : ((-217607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36782328817/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-217607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c141 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-458627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6829819/10000000) (δ := 10881/1000000000) (ψ := -1426207/1000000) 215 170
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t141 : ((-12070459347/156250000000 : ℚ) : ℝ) ≤ stT215 141 := by
  have hc : ((-114663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12070459347/156250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-114663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c142 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((175349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3031199/10000000) (δ := 10881/1000000000) (ψ := -1426207/1000000) 215 170
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t142 : ((36782142411/1250000000000 : ℚ) : ℝ) ≤ stT215 142 := by
  have hc : ((43831/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36782142411/1250000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((43831/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c143 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((478211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740761/10000000) (δ := 10881/1000000000) (ψ := -1426207/1000000) 215 170
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t143 : ((99969804253/1250000000000 : ℚ) : ℝ) ≤ stT215 143 := by
  have hc : ((239093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99969804253/1250000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((239093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c144 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-44379/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280399/625000) (δ := 5411/500000000) (ψ := -1426207/1000000) 215 170
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t144 : ((-18495431463/1000000000000 : ℚ) : ℝ) ≤ stT215 144 := by
  have hc : ((-44389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18495431463/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-44389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c145 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-495047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7501811/10000000) (δ := 5437/500000000) (ψ := -1426207/1000000) 215 171
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t145 : ((-2569593861/31250000000 : ℚ) : ℝ) ≤ stT215 145 := by
  have hc : ((-15471/15625 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2569593861/31250000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-15471/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c146 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((47727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3807627/10000000) (δ := 5387/500000000) (ψ := -1426207/1000000) 215 171
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t146 : ((7891544717/2000000000000 : ℚ) : ℝ) ≤ stT215 146 := by
  have hc : ((47677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7891544717/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((47677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c147 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((998461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69353/5000000) (δ := 5437/500000000) (ψ := -1426207/1000000) 215 171
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t147 : ((411737707523/5000000000000 : ℚ) : ℝ) ≤ stT215 147 := by
  have hc : ((998411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411737707523/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((998411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c148 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((33569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3505383/10000000) (δ := 5387/500000000) (ψ := -1426207/1000000) 215 171
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t148 : ((13792648323/1000000000000 : ℚ) : ℝ) ≤ stT215 148 := by
  have hc : ((33559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13792648323/1000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((33559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c149 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-957783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3562481/5000000) (δ := 10829/1000000000) (ψ := -1426207/1000000) 215 171
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t149 : ((-24521482633/312500000000 : ℚ) : ℝ) ≤ stT215 149 := by
  have hc : ((-957833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24521482633/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-957833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c150 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-16467/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2493859/5000000) (δ := 10867/1000000000) (ψ := -1426207/1000000) 215 172
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t150 : ((-13446889093/400000000000 : ℚ) : ℝ) ≤ stT215 150 := by
  have hc : ((-16469/40000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13446889093/400000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-16469/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c151 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((421893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283249/2000000) (δ := 2709/250000000) (ψ := -1426207/1000000) 215 172
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t151 : ((21456944749/312500000000 : ℚ) : ℝ) ≤ stT215 151 := by
  have hc : ((105467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21456944749/312500000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((105467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c152 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((164497/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2131631/10000000) (δ := 10767/1000000000) (ψ := -1426207/1000000) 215 172
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t152 : ((266829058683/5000000000000 : ℚ) : ℝ) ≤ stT215 152 := by
  have hc : ((328969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266829058683/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((328969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c153 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-127569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2828117/5000000) (δ := 1367/125000000) (ψ := -1426207/1000000) 215 172
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t153 : ((-103141625287/2000000000000 : ℚ) : ℝ) ≤ stT215 153 := by
  have hc : ((-127579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103141625287/2000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-127579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c154 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-433521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3275039/5000000) (δ := 171/15625000) (ψ := -1426207/1000000) 215 173
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t154 : ((-174680669179/2500000000000 : ℚ) : ℝ) ≤ stT215 154 := by
  have hc : ((-216773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174680669179/2500000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-216773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c155 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((41963/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -307111/1000000) (δ := 10859/1000000000) (ψ := -1426207/1000000) 215 173
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t155 : ((134801835113/5000000000000 : ℚ) : ℝ) ≤ stT215 155 := by
  have hc : ((167827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134801835113/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((167827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c156 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((197627/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385499/10000000) (δ := 10759/1000000000) (ψ := -1426207/1000000) 215 173
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t156 : ((247218867/3125000000 : ℚ) : ℝ) ≤ stT215 156 := by
  have hc : ((197617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247218867/3125000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((197617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c157 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((5347/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3820017/10000000) (δ := 171/15625000) (ψ := -1426207/1000000) 215 173
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t157 : ((8524755609/2500000000000 : ℚ) : ℝ) ≤ stT215 157 := by
  have hc : ((21363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8524755609/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((21363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c158 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-969281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904089/1250000) (δ := 171/15625000) (ψ := -1426207/1000000) 215 173
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t158 : ((-385579515849/5000000000000 : ℚ) : ℝ) ≤ stT215 158 := by
  have hc : ((-969331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385579515849/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-969331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c159 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-446479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5084057/10000000) (δ := 2713/250000000) (ψ := -1426207/1000000) 215 174
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t159 : ((-88530179127/2500000000000 : ℚ) : ℝ) ≤ stT215 159 := by
  have hc : ((-446529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88530179127/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-446529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c160 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((387001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1714147/10000000) (δ := 2713/250000000) (ψ := -1426207/1000000) 215 174
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t160 : ((9560350917/156250000000 : ℚ) : ℝ) ≤ stT215 160 := by
  have hc : ((12093/15625 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9560350917/156250000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((12093/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c161 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((396859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1634747/10000000) (δ := 21/1953125) (ψ := -1426207/1000000) 215 174
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t161 : ((15637442187/250000000000 : ℚ) : ℝ) ≤ stT215 161 := by
  have hc : ((198417/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15637442187/250000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((198417/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c162 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-3221/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4962947/10000000) (δ := 21/1953125) (ψ := -1426207/1000000) 215 174
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t162 : ((-506194689/16000000000 : ℚ) : ℝ) ≤ stT215 162 := by
  have hc : ((-16107/40000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506194689/16000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-16107/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c163 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-493071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1487459/2000000) (δ := 5379/500000000) (ψ := -1426207/1000000) 215 175
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t163 : ((-48277858257/625000000000 : ℚ) : ℝ) ≤ stT215 163 := by
  have hc : ((-61637/62500 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48277858257/625000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-61637/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c164 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-89021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2074919/5000000) (δ := 2189/200000000) (ψ := -1426207/1000000) 215 175
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t164 : ((-69552782699/10000000000000 : ℚ) : ℝ) ≤ stT215 164 := by
  have hc : ((-89071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69552782699/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-89071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c165 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((938357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7059/80000) (δ := 5379/500000000) (ψ := -1426207/1000000) 215 175
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t165 : ((365235061443/5000000000000 : ℚ) : ℝ) ≤ stT215 165 := by
  have hc : ((938307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365235061443/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((938307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c166 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((116963/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2365361/10000000) (δ := 2169/200000000) (ψ := -1426207/1000000) 215 175
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t166 : ((1815461419/40000000000 : ℚ) : ℝ) ≤ stT215 166 := by
  have hc : ((116953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1815461419/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((116953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c167 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-154591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139841/250000) (δ := 5379/500000000) (ψ := -1426207/1000000) 215 175
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t167 : ((-3738621837/78125000000 : ℚ) : ℝ) ≤ stT215 167 := by
  have hc : ((-309207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3738621837/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-309207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c168 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-464437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1381079/2000000) (δ := 5469/500000000) (ψ := -1426207/1000000) 215 176
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t168 : ((-179170164427/2500000000000 : ℚ) : ℝ) ≤ stT215 168 := by
  have hc : ((-232231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179170164427/2500000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-232231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c169 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((84519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46443/125000) (δ := 5469/500000000) (ψ := -1426207/1000000) 215 176
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t169 : ((6497608887/1000000000000 : ℚ) : ℝ) ≤ stT215 169 := by
  have hc : ((84469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6497608887/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((84469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c170 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((244097/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544351/10000000) (δ := 5419/500000000) (ψ := -1426207/1000000) 215 176
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t170 : ((93602012229/1250000000000 : ℚ) : ℝ) ≤ stT215 170 := by
  have hc : ((488169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93602012229/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((488169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c171 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((50341/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130407/500000) (δ := 5469/500000000) (ψ := -1426207/1000000) 215 176
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t171 : ((1202902987/31250000000 : ℚ) : ℝ) ≤ stT215 171 := by
  have hc : ((1573/3125 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1202902987/31250000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((1573/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c172 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-663961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5742249/10000000) (δ := 5419/500000000) (ψ := -1426207/1000000) 215 176
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t172 : ((-506303739423/10000000000000 : ℚ) : ℝ) ≤ stT215 172 := by
  have hc : ((-664011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506303739423/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-664011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c173 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-230101/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6849773/10000000) (δ := 10831/1000000000) (ψ := -1426207/1000000) 215 177
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t173 : ((-174952072461/2500000000000 : ℚ) : ℝ) ≤ stT215 173 := by
  have hc : ((-460227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174952072461/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-460227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c174 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((2801/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -468973/1250000) (δ := 2693/250000000) (ψ := -1426207/1000000) 215 177
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t174 : ((1060958151/200000000000 : ℚ) : ℝ) ≤ stT215 174 := by
  have hc : ((2799/40000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1060958151/200000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((2799/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c175 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((48207/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671533/10000000) (δ := 10831/1000000000) (ψ := -1426207/1000000) 215 177
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t175 : ((9109782819/125000000000 : ℚ) : ℝ) ≤ stT215 175 := by
  have hc : ((96409/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9109782819/125000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((96409/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c176 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((576419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195571/5000000) (δ := 10831/1000000000) (ψ := -1426207/1000000) 215 177
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t176 : ((217227136041/5000000000000 : ℚ) : ℝ) ≤ stT215 176 := by
  have hc : ((576369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217227136041/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((576369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c177 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-567781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 543651/1000000) (δ := 1359/125000000) (ψ := -1426207/1000000) 215 177
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t177 : ((-426808467657/10000000000000 : ℚ) : ℝ) ≤ stT215 177 := by
  have hc : ((-567831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426808467657/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-567831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c178 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-121289/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3621643/5000000) (δ := 10779/1000000000) (ψ := -1426207/1000000) 215 178
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t178 : ((-90914671323/1250000000000 : ℚ) : ℝ) ≤ stT215 178 := by
  have hc : ((-485181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90914671323/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-485181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c179 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-121721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84641/200000) (δ := 1353/125000000) (ψ := -1426207/1000000) 215 178
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t179 : ((-22754007289/2500000000000 : ℚ) : ℝ) ≤ stT215 179 := by
  have hc : ((-121771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22754007289/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-121771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c180 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((879943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1237637/10000000) (δ := 10879/1000000000) (ψ := -1426207/1000000) 215 178
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t180 : ((131166529403/2000000000000 : ℚ) : ℝ) ≤ stT215 180 := by
  have hc : ((879893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131166529403/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((879893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c181 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((767357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 87011/500000) (δ := 1353/125000000) (ψ := -1426207/1000000) 215 178
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t181 : ((285167344629/5000000000000 : ℚ) : ℝ) ≤ stT215 181 := by
  have hc : ((767307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285167344629/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((767307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c182 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-304921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 470163/1000000) (δ := 1353/125000000) (ψ := -1426207/1000000) 215 178
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t182 : ((-180847803/8000000000 : ℚ) : ℝ) ≤ stT215 182 := by
  have hc : ((-304971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180847803/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-304971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c183 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-99657/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7646861/10000000) (δ := 2731/250000000) (ψ := -1426207/1000000) 215 178
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t183 : ((-18418085741/250000000000 : ℚ) : ℝ) ≤ stT215 183 := by
  have hc : ((-49831/50000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18418085741/250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-49831/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c184 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-92707/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2565971/5000000) (δ := 169/15625000) (ψ := -1426207/1000000) 215 179
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t184 : ((-6835189957/200000000000 : ℚ) : ℝ) ≤ stT215 184 := by
  have hc : ((-92717/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6835189957/200000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-92717/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c185 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((631387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1109319/5000000) (δ := 10787/1000000000) (ψ := -1426207/1000000) 215 179
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t185 : ((232083900559/5000000000000 : ℚ) : ℝ) ≤ stT215 185 := by
  have hc : ((631337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232083900559/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((631337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c186 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((120419/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 678917/10000000) (δ := 10787/1000000000) (ψ := -1426207/1000000) 215 179
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t186 : ((70632674197/1000000000000 : ℚ) : ℝ) ≤ stT215 186 := by
  have hc : ((481651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70632674197/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((481651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c187 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((145877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111281/312500) (δ := 10787/1000000000) (ψ := -1426207/1000000) 215 179
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t187 : ((13329900243/1250000000000 : ℚ) : ℝ) ≤ stT215 187 := by
  have hc : ((145827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13329900243/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((145827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c188 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-841611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6427641/10000000) (δ := 10887/1000000000) (ψ := -1426207/1000000) 215 179
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t188 : ((-24553776353/400000000000 : ℚ) : ℝ) ≤ stT215 188 := by
  have hc : ((-841661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24553776353/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-841661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c189 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-210467/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6428831/10000000) (δ := 5447/500000000) (ψ := -1426207/1000000) 215 180
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t189 : ((-306202629887/5000000000000 : ℚ) : ℝ) ≤ stT215 189 := by
  have hc : ((-420959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306202629887/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-420959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c190 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((6671/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -898111/2500000) (δ := 10809/1000000000) (ψ := -1426207/1000000) 215 180
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t190 : ((2418918353/250000000000 : ℚ) : ℝ) ≤ stT215 190 := by
  have hc : ((13337/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2418918353/250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((13337/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c191 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((476417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -770891/10000000) (δ := 5447/500000000) (ψ := -1426207/1000000) 215 180
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t191 : ((21544054063/312500000000 : ℚ) : ℝ) ≤ stT215 191 := by
  have hc : ((59549/62500 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21544054063/312500000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((59549/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c192 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((34317/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50897/250000) (δ := 5397/500000000) (ψ := -1426207/1000000) 215 180
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t192 : ((49528657123/1000000000000 : ℚ) : ℝ) ≤ stT215 192 := by
  have hc : ((68629/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49528657123/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((68629/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c193 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-88171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 965617/2000000) (δ := 5397/500000000) (ψ := -1426207/1000000) 215 180
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t193 : ((-15868973559/625000000000 : ℚ) : ℝ) ≤ stT215 193 := by
  have hc : ((-176367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15868973559/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-176367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c194 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-24877/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1521177/2000000) (δ := 5397/500000000) (ψ := -1426207/1000000) 215 180
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t194 : ((-71446253967/1000000000000 : ℚ) : ℝ) ≤ stT215 194 := by
  have hc : ((-99513/100000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71446253967/1000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-99513/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c195 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-535107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -333661/625000) (δ := 5401/500000000) (ψ := -1426207/1000000) 215 181
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t195 : ((-76646791011/2000000000000 : ℚ) : ℝ) ≤ stT215 195 := by
  have hc : ((-535157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76646791011/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-535157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c196 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((254969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258921/1000000) (δ := 5451/500000000) (ψ := -1426207/1000000) 215 181
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t196 : ((1138141719/31250000000 : ℚ) : ℝ) ≤ stT215 196 := by
  have hc : ((7967/15625 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1138141719/31250000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((7967/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c197 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((998291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73091/5000000) (δ := 10901/1000000000) (ψ := -1426207/1000000) 215 181
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t197 : ((71121676527/1000000000000 : ℚ) : ℝ) ≤ stT215 197 := by
  have hc : ((998241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71121676527/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((998241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c198 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((411149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 573541/2000000) (δ := 5451/500000000) (ψ := -1426207/1000000) 215 181
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t198 : ((292155315231/10000000000000 : ℚ) : ℝ) ≤ stT215 198 := by
  have hc : ((411099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292155315231/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((411099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c199 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-612653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5575523/10000000) (δ := 10801/1000000000) (ψ := -1426207/1000000) 215 181
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t199 : ((-217167064023/5000000000000 : ℚ) : ℝ) ≤ stT215 199 := by
  have hc : ((-612703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217167064023/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-612703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c200 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-986203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3719111/5000000) (δ := 2179/200000000) (ψ := -1426207/1000000) 215 182
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t200 : ((-697386400071/10000000000000 : ℚ) : ℝ) ≤ stT215 200 := by
  have hc : ((-986253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-697386400071/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-986253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c201 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-81521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4757387/10000000) (δ := 2179/200000000) (ψ := -1426207/1000000) 215 182
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t201 : ((-57509328091/2500000000000 : ℚ) : ℝ) ≤ stT215 201 := by
  have hc : ((-163067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57509328091/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-163067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c202 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((134091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417987/2000000) (δ := 2727/250000000) (ψ := -1426207/1000000) 215 182
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t202 : ((94338989357/2000000000000 : ℚ) : ℝ) ≤ stT215 202 := by
  have hc : ((134081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94338989357/2000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((134081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c203 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((30457/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 564401/10000000) (δ := 1351/125000000) (ψ := -1426207/1000000) 215 182
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t203 : ((171004114197/2500000000000 : ℚ) : ℝ) ≤ stT215 203 := by
  have hc : ((487287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171004114197/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((487287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c204 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((284539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 801419/2500000) (δ := 1351/125000000) (ψ := -1426207/1000000) 215 182
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t204 : ((9959106423/500000000000 : ℚ) : ℝ) ≤ stT215 204 := by
  have hc : ((284489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9959106423/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((284489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c205 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-345483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5834051/10000000) (δ := 1351/125000000) (ψ := -1426207/1000000) 215 182
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t205 : ((-60328374487/1250000000000 : ℚ) : ℝ) ≤ stT215 205 := by
  have hc : ((-86377/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60328374487/1250000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-86377/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c206 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-3887/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -725833/1000000) (δ := 2697/250000000) (ψ := -1426207/1000000) 215 183
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t206 : ((-1692715253/25000000000 : ℚ) : ℝ) ≤ stT215 206 := by
  have hc : ((-4859/5000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1692715253/25000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-4859/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c207 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-287271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581929/1250000) (δ := 2183/200000000) (ψ := -1426207/1000000) 215 183
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t207 : ((-199702173729/10000000000000 : ℚ) : ℝ) ≤ stT215 207 := by
  have hc : ((-287321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199702173729/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-287321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c208 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((135561/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2065059/10000000) (δ := 1361/125000000) (ψ := -1426207/1000000) 215 183
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t208 : ((751901397/16000000000 : ℚ) : ℝ) ≤ stT215 208 := by
  have hc : ((135551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((751901397/16000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((135551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c209 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((244757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 512899/10000000) (δ := 2163/200000000) (ψ := -1426207/1000000) 215 183
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t209 : ((169293197073/2500000000000 : ℚ) : ℝ) ≤ stT215 209 := by
  have hc : ((489489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169293197073/2500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((489489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c210 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((3329/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769637/2500000) (δ := 2183/200000000) (ψ := -1426207/1000000) 215 183
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t210 : ((918752541/40000000000 : ℚ) : ℝ) ≤ stT215 210 := by
  have hc : ((6657/20000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((918752541/40000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((6657/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c211 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-157587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1126399/2000000) (δ := 2697/250000000) (ψ := -1426207/1000000) 215 183
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t211 : ((-216992132371/5000000000000 : ℚ) : ℝ) ≤ stT215 211 := by
  have hc : ((-315199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216992132371/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-315199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c212 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-991851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3767307/5000000) (δ := 10923/1000000000) (ψ := -1426207/1000000) 215 184
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t212 : ((-681240582503/10000000000000 : ℚ) : ℝ) ≤ stT215 212 := by
  have hc : ((-991901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-681240582503/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-991901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c213 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-83607/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5005193/10000000) (δ := 10823/1000000000) (ψ := -1426207/1000000) 215 184
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t213 : ((-57293448613/2000000000000 : ℚ) : ℝ) ≤ stT215 213 := by
  have hc : ((-83617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57293448613/2000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-83617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c214 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((54447/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2487597/10000000) (δ := 539/50000000) (ψ := -1426207/1000000) 215 184
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t214 : ((3721573457/100000000000 : ℚ) : ℝ) ≤ stT215 214 := by
  have hc : ((27221/50000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3721573457/100000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((27221/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c215 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((999973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4557/2500000) (δ := 539/50000000) (ψ := -1426207/1000000) 215 184
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t215 : ((340970743231/5000000000000 : ℚ) : ℝ) ≤ stT215 215 := by
  have hc : ((999923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340970743231/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((999923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c216 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((536107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2512443/10000000) (δ := 539/50000000) (ψ := -1426207/1000000) 215 184
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t216 : ((364740151541/10000000000000 : ℚ) : ℝ) ≤ stT215 216 := by
  have hc : ((536057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364740151541/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((536057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c217 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-82873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2497551/5000000) (δ := 10823/1000000000) (ψ := -1426207/1000000) 215 184
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t217 : ((-11252942027/400000000000 : ℚ) : ℝ) ≤ stT215 217 := by
  have hc : ((-82883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11252942027/400000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-82883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c218 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-247001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3733183/5000000) (δ := 10923/1000000000) (ψ := -1426207/1000000) 215 184
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t218 : ((-167298785361/2500000000000 : ℚ) : ℝ) ≤ stT215 218 := by
  have hc : ((-494027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167298785361/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-494027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c219 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-337827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5781621/10000000) (δ := 1093/100000000) (ψ := -1426207/1000000) 215 185
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t219 : ((-28537429347/625000000000 : ℚ) : ℝ) ≤ stT215 219 := by
  have hc : ((-84463/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28537429347/625000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-84463/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c220 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((117707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3332879/10000000) (δ := 10773/1000000000) (ψ := -1426207/1000000) 215 185
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t220 : ((39670543359/2500000000000 : ℚ) : ℝ) ≤ stT215 220 := by
  have hc : ((58841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39670543359/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((58841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c221 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((93657/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895209/10000000) (δ := 10773/1000000000) (ψ := -1426207/1000000) 215 185
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t221 : ((492164673/7812500000 : ℚ) : ℝ) ≤ stT215 221 := by
  have hc : ((23413/25000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((492164673/7812500000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((23413/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c222 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((818181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1531389/10000000) (δ := 1093/100000000) (ψ := -1426207/1000000) 215 185
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t222 : ((137273382359/2500000000000 : ℚ) : ℝ) ≤ stT215 222 := by
  have hc : ((818131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137273382359/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((818131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c223 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-1611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3947129/10000000) (δ := 1093/100000000) (ψ := -1426207/1000000) 215 185
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t223 : ((-21710053/40000000000 : ℚ) : ℝ) ≤ stT215 223 := by
  have hc : ((-1621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21710053/40000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-1621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c224 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-412451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1270413/2000000) (δ := 1083/100000000) (ψ := -1426207/1000000) 215 185
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t224 : ((-34449686163/625000000000 : ℚ) : ℝ) ≤ stT215 224 := by
  have hc : ((-103119/125000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34449686163/625000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-103119/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c225 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-468487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3480829/5000000) (δ := 10937/1000000000) (ψ := -1426207/1000000) 215 186
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t225 : ((-9760671547/156250000000 : ℚ) : ℝ) ≤ stT215 225 := by
  have hc : ((-14641/15625 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9760671547/156250000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-14641/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c226 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-51501/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -572261/1250000) (δ := 10783/500000000) (ψ := -1426207/1000000) 215 186
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t226 : ((-34264653601/2000000000000 : ℚ) : ℝ) ≤ stT215 226 := by
  have hc : ((-51511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34264653601/2000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-51511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c227 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((635609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102499/5000000) (δ := 10937/1000000000) (ψ := -1426207/1000000) 215 186
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t227 : ((421835126157/10000000000000 : ℚ) : ℝ) ≤ stT215 227 := by
  have hc : ((635559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421835126157/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((635559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c228 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((998013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157637/10000000) (δ := 10937/1000000000) (ψ := -1426207/1000000) 215 186
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t228 : ((330458482079/5000000000000 : ℚ) : ℝ) ≤ stT215 228 := by
  have hc : ((997963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330458482079/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((997963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c229 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((134237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19609/78125) (δ := 10937/1000000000) (ψ := -1426207/1000000) 215 186
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t229 : ((88697965641/2500000000000 : ℚ) : ℝ) ≤ stT215 229 := by
  have hc : ((268449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88697965641/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((268449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c230 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-361619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1213/2500) (δ := 5433/500000000) (ψ := -1426207/1000000) 215 186
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t230 : ((-238477666889/10000000000000 : ℚ) : ℝ) ≤ stT215 230 := by
  have hc : ((-361669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238477666889/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-361669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c231 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-964293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 718389/1000000) (δ := 5433/500000000) (ψ := -1426207/1000000) 215 186
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t231 : ((-19827856423/312500000000 : ℚ) : ℝ) ≤ stT215 231 := by
  have hc : ((-964343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19827856423/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-964343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c232 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-789577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387643/625000) (δ := 10759/1000000000) (ψ := -1426207/1000000) 215 187
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t232 : ((-518416183191/10000000000000 : ℚ) : ℝ) ≤ stT215 232 := by
  have hc : ((-789627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518416183191/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-789627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c233 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((14617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3890447/10000000) (δ := 10859/1000000000) (ψ := -1426207/1000000) 215 187
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t233 : ((9543147607/10000000000000 : ℚ) : ℝ) ≤ stT215 233 := by
  have hc : ((14567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9543147607/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((14567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c234 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((201209/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317699/2000000) (δ := 171/15625000) (ψ := -1426207/1000000) 215 187
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t234 : ((6576308799/125000000000 : ℚ) : ℝ) ≤ stT215 234 := by
  have hc : ((402393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6576308799/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((402393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c235 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((480327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35181/500000) (δ := 171/15625000) (ψ := -1426207/1000000) 215 187
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t235 : ((19582152691/312500000000 : ℚ) : ℝ) ≤ stT215 235 := by
  have hc : ((240151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19582152691/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((240151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c236 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((367569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493003/5000000) (δ := 2711/250000000) (ψ := -1426207/1000000) 215 187
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t236 : ((3738035749/156250000000 : ℚ) : ℝ) ≤ stT215 236 := by
  have hc : ((367519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3738035749/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((367519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c237 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-507853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5258717/10000000) (δ := 10759/1000000000) (ψ := -1426207/1000000) 215 187
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t237 : ((-32991855171/1000000000000 : ℚ) : ℝ) ≤ stT215 237 := by
  have hc : ((-507903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32991855171/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-507903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c238 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-991189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7521861/10000000) (δ := 2711/250000000) (ψ := -1426207/1000000) 215 187
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t238 : ((-160631271189/2500000000000 : ℚ) : ℝ) ≤ stT215 238 := by
  have hc : ((-991239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160631271189/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-991239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c239 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-718867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5932419/10000000) (δ := 2713/250000000) (ψ := -1426207/1000000) 215 188
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t239 : ((-465029304699/10000000000000 : ℚ) : ℝ) ≤ stT215 239 := by
  have hc : ((-718917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465029304699/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-718917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c240 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((19079/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3688141/10000000) (δ := 10851/1000000000) (ψ := -1426207/1000000) 215 188
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t240 : ((12308982293/2000000000000 : ℚ) : ℝ) ≤ stT215 240 := by
  have hc : ((19069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12308982293/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((19069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c241 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((835757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45413/312500) (δ := 10851/1000000000) (ψ := -1426207/1000000) 215 188
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t241 : ((134581419573/2500000000000 : ℚ) : ℝ) ≤ stT215 241 := by
  have hc : ((835707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134581419573/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((835707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c242 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((952643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48279/625000) (δ := 10851/1000000000) (ψ := -1426207/1000000) 215 188
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t242 : ((76543705329/1250000000000 : ℚ) : ℝ) ≤ stT215 242 := by
  have hc : ((952593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76543705329/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((952593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c243 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((366473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2988953/10000000) (δ := 10951/1000000000) (ψ := -1426207/1000000) 215 188
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t243 : ((470120709/20000000000 : ℚ) : ℝ) ≤ stT215 243 := by
  have hc : ((366423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((470120709/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((366423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c244 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-48621/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2598179/5000000) (δ := 10951/1000000000) (ψ := -1426207/1000000) 215 188
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t244 : ((-3112963581/100000000000 : ℚ) : ℝ) ≤ stT215 244 := by
  have hc : ((-24313/50000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3112963581/100000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-24313/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c245 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-983173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3697353/5000000) (δ := 21651/1000000000) (ψ := -1426207/1000000) 215 188
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t245 : ((-628158560571/10000000000000 : ℚ) : ℝ) ≤ stT215 245 := by
  have hc : ((-983223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-628158560571/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-983223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c246 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-769933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -765479/1250000) (δ := 5379/500000000) (ψ := -1426207/1000000) 215 189
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t246 : ((-490923451191/10000000000000 : ℚ) : ℝ) ≤ stT215 246 := by
  have hc : ((-769983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490923451191/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-769983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c247 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((-1631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1971651/5000000) (δ := 5379/500000000) (ψ := -1426207/1000000) 215 189
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t247 : ((-418293759/1000000000000 : ℚ) : ℝ) ≤ stT215 247 := by
  have hc : ((-3287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418293759/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-3287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c248 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((759251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1771587/10000000) (δ := 5379/500000000) (ψ := -1426207/1000000) 215 189
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t248 : ((96418527/2000000000 : ℚ) : ℝ) ≤ stT215 248 := by
  have hc : ((759201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96418527/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((759201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c249 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((246943/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391367/10000000) (δ := 5429/500000000) (ψ := -1426207/1000000) 215 189
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t249 : ((78242892091/1250000000000 : ℚ) : ℝ) ≤ stT215 249 := by
  have hc : ((493861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78242892091/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((493861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_c250 :
    |Real.cos (((215 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((65603/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63643/250000) (δ := 2189/200000000) (ψ := -1426207/1000000) 215 189
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st215_t250 : ((33189594017/1000000000000 : ℚ) : ℝ) ≤ stT215 250 := by
  have hc : ((262387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((215 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st215_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33189594017/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((262387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st215_p1 : ((36009/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT215 (i+1) := by
  rw [Finset.sum_range_one]
  exact st215_t1

theorem st215_p2 : ((8097748367299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT215 (i+1))
      = (∑ i ∈ Finset.range 1, stT215 (i+1)) + stT215 2 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 1
    simpa using h
  have hprev := st215_p1
  have hstep := st215_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p3 : ((421762248809/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT215 (i+1))
      = (∑ i ∈ Finset.range 2, stT215 (i+1)) + stT215 3 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 2
    simpa using h
  have hprev := st215_p2
  have hstep := st215_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p4 : ((3980980351903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT215 (i+1))
      = (∑ i ∈ Finset.range 3, stT215 (i+1)) + stT215 4 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 3
    simpa using h
  have hprev := st215_p3
  have hstep := st215_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p5 : ((660012373763/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT215 (i+1))
      = (∑ i ∈ Finset.range 4, stT215 (i+1)) + stT215 5 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 4
    simpa using h
  have hprev := st215_p4
  have hstep := st215_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p6 : ((82283912247/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT215 (i+1))
      = (∑ i ∈ Finset.range 5, stT215 (i+1)) + stT215 6 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 5
    simpa using h
  have hprev := st215_p5
  have hstep := st215_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p7 : ((2042392989/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT215 (i+1))
      = (∑ i ∈ Finset.range 6, stT215 (i+1)) + stT215 7 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 6
    simpa using h
  have hprev := st215_p6
  have hstep := st215_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p8 : ((738783266889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT215 (i+1))
      = (∑ i ∈ Finset.range 7, stT215 (i+1)) + stT215 8 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 7
    simpa using h
  have hprev := st215_p7
  have hstep := st215_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p9 : ((-340649341897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT215 (i+1))
      = (∑ i ∈ Finset.range 8, stT215 (i+1)) + stT215 9 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 8
    simpa using h
  have hprev := st215_p8
  have hstep := st215_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p10 : ((1780285387571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT215 (i+1))
      = (∑ i ∈ Finset.range 9, stT215 (i+1)) + stT215 10 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 9
    simpa using h
  have hprev := st215_p9
  have hstep := st215_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p11 : ((1235315592527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT215 (i+1))
      = (∑ i ∈ Finset.range 10, stT215 (i+1)) + stT215 11 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 10
    simpa using h
  have hprev := st215_p10
  have hstep := st215_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p12 : ((1120916497519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT215 (i+1))
      = (∑ i ∈ Finset.range 11, stT215 (i+1)) + stT215 12 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 11
    simpa using h
  have hprev := st215_p11
  have hstep := st215_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p13 : ((3893029747519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT215 (i+1))
      = (∑ i ∈ Finset.range 12, stT215 (i+1)) + stT215 13 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 12
    simpa using h
  have hprev := st215_p12
  have hstep := st215_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p14 : ((1271073454321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT215 (i+1))
      = (∑ i ∈ Finset.range 13, stT215 (i+1)) + stT215 14 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 13
    simpa using h
  have hprev := st215_p13
  have hstep := st215_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p15 : ((3279888520189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT215 (i+1))
      = (∑ i ∈ Finset.range 14, stT215 (i+1)) + stT215 15 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 14
    simpa using h
  have hprev := st215_p14
  have hstep := st215_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p16 : ((5299561020189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT215 (i+1))
      = (∑ i ∈ Finset.range 15, stT215 (i+1)) + stT215 16 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 15
    simpa using h
  have hprev := st215_p15
  have hstep := st215_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p17 : ((1280734076841/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT215 (i+1))
      = (∑ i ∈ Finset.range 16, stT215 (i+1)) + stT215 17 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 16
    simpa using h
  have hprev := st215_p16
  have hstep := st215_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p18 : ((1602040958859/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT215 (i+1))
      = (∑ i ∈ Finset.range 17, stT215 (i+1)) + stT215 18 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 17
    simpa using h
  have hprev := st215_p17
  have hstep := st215_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p19 : ((10287435503949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT215 (i+1))
      = (∑ i ∈ Finset.range 18, stT215 (i+1)) + stT215 19 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 18
    simpa using h
  have hprev := st215_p18
  have hstep := st215_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p20 : ((10089355656237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT215 (i+1))
      = (∑ i ∈ Finset.range 19, stT215 (i+1)) + stT215 20 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 19
    simpa using h
  have hprev := st215_p19
  have hstep := st215_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p21 : ((828126105567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT215 (i+1))
      = (∑ i ∈ Finset.range 20, stT215 (i+1)) + stT215 21 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 20
    simpa using h
  have hprev := st215_p20
  have hstep := st215_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p22 : ((1041284165427/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT215 (i+1))
      = (∑ i ∈ Finset.range 21, stT215 (i+1)) + stT215 22 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 21
    simpa using h
  have hprev := st215_p21
  have hstep := st215_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p23 : ((1668275458123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT215 (i+1))
      = (∑ i ∈ Finset.range 22, stT215 (i+1)) + stT215 23 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 22
    simpa using h
  have hprev := st215_p22
  have hstep := st215_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p24 : ((5178317666963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT215 (i+1))
      = (∑ i ∈ Finset.range 23, stT215 (i+1)) + stT215 24 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 23
    simpa using h
  have hprev := st215_p23
  have hstep := st215_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p25 : ((8973864642541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT215 (i+1))
      = (∑ i ∈ Finset.range 24, stT215 (i+1)) + stT215 25 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 24
    simpa using h
  have hprev := st215_p24
  have hstep := st215_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p26 : ((8528588693927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT215 (i+1))
      = (∑ i ∈ Finset.range 25, stT215 (i+1)) + stT215 26 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 25
    simpa using h
  have hprev := st215_p25
  have hstep := st215_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p27 : ((10452057161927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT215 (i+1))
      = (∑ i ∈ Finset.range 26, stT215 (i+1)) + stT215 27 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 26
    simpa using h
  have hprev := st215_p26
  have hstep := st215_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p28 : ((10459023045819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT215 (i+1))
      = (∑ i ∈ Finset.range 27, stT215 (i+1)) + stT215 28 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 27
    simpa using h
  have hprev := st215_p27
  have hstep := st215_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p29 : ((8692248302921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT215 (i+1))
      = (∑ i ∈ Finset.range 28, stT215 (i+1)) + stT215 29 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 28
    simpa using h
  have hprev := st215_p28
  have hstep := st215_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p30 : ((7287027632039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT215 (i+1))
      = (∑ i ∈ Finset.range 29, stT215 (i+1)) + stT215 30 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 29
    simpa using h
  have hprev := st215_p29
  have hstep := st215_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p31 : ((7086905907197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT215 (i+1))
      = (∑ i ∈ Finset.range 30, stT215 (i+1)) + stT215 31 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 30
    simpa using h
  have hprev := st215_p30
  have hstep := st215_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p32 : ((7825644712001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT215 (i+1))
      = (∑ i ∈ Finset.range 31, stT215 (i+1)) + stT215 32 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 31
    simpa using h
  have hprev := st215_p31
  have hstep := st215_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p33 : ((9029713359561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT215 (i+1))
      = (∑ i ∈ Finset.range 32, stT215 (i+1)) + stT215 33 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 32
    simpa using h
  have hprev := st215_p32
  have hstep := st215_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p34 : ((5186030636903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT215 (i+1))
      = (∑ i ∈ Finset.range 33, stT215 (i+1)) + stT215 34 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 33
    simpa using h
  have hprev := st215_p33
  have hstep := st215_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p35 : ((5819946000989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT215 (i+1))
      = (∑ i ∈ Finset.range 34, stT215 (i+1)) + stT215 35 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 34
    simpa using h
  have hprev := st215_p34
  have hstep := st215_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p36 : ((630530997351/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT215 (i+1))
      = (∑ i ∈ Finset.range 35, stT215 (i+1)) + stT215 36 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 35
    simpa using h
  have hprev := st215_p35
  have hstep := st215_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p37 : ((3246086169603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT215 (i+1))
      = (∑ i ∈ Finset.range 36, stT215 (i+1)) + stT215 37 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 36
    simpa using h
  have hprev := st215_p36
  have hstep := st215_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p38 : ((12473757373807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT215 (i+1))
      = (∑ i ∈ Finset.range 37, stT215 (i+1)) + stT215 38 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 37
    simpa using h
  have hprev := st215_p37
  have hstep := st215_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p39 : ((11110395454649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT215 (i+1))
      = (∑ i ∈ Finset.range 38, stT215 (i+1)) + stT215 39 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 38
    simpa using h
  have hprev := st215_p38
  have hstep := st215_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p40 : ((9594143236931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT215 (i+1))
      = (∑ i ∈ Finset.range 39, stT215 (i+1)) + stT215 40 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 39
    simpa using h
  have hprev := st215_p39
  have hstep := st215_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p41 : ((9119328032791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT215 (i+1))
      = (∑ i ∈ Finset.range 40, stT215 (i+1)) + stT215 41 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 40
    simpa using h
  have hprev := st215_p40
  have hstep := st215_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p42 : ((10218964328109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT215 (i+1))
      = (∑ i ∈ Finset.range 41, stT215 (i+1)) + stT215 42 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 41
    simpa using h
  have hprev := st215_p41
  have hstep := st215_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p43 : ((1449282671933/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT215 (i+1))
      = (∑ i ∈ Finset.range 42, stT215 (i+1)) + stT215 43 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 42
    simpa using h
  have hprev := st215_p42
  have hstep := st215_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p44 : ((11270620546261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT215 (i+1))
      = (∑ i ∈ Finset.range 43, stT215 (i+1)) + stT215 44 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 43
    simpa using h
  have hprev := st215_p43
  have hstep := st215_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p45 : ((9786849301333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT215 (i+1))
      = (∑ i ∈ Finset.range 44, stT215 (i+1)) + stT215 45 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 44
    simpa using h
  have hprev := st215_p44
  have hstep := st215_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p46 : ((9910443948427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT215 (i+1))
      = (∑ i ∈ Finset.range 45, stT215 (i+1)) + stT215 46 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 45
    simpa using h
  have hprev := st215_p45
  have hstep := st215_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p47 : ((1134736928887/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT215 (i+1))
      = (∑ i ∈ Finset.range 46, stT215 (i+1)) + stT215 47 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 46
    simpa using h
  have hprev := st215_p46
  have hstep := st215_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p48 : ((5420486183139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT215 (i+1))
      = (∑ i ∈ Finset.range 47, stT215 (i+1)) + stT215 48 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 47
    simpa using h
  have hprev := st215_p47
  have hstep := st215_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p49 : ((4846535953559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT215 (i+1))
      = (∑ i ∈ Finset.range 48, stT215 (i+1)) + stT215 49 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 48
    simpa using h
  have hprev := st215_p48
  have hstep := st215_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p50 : ((5443967406983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT215 (i+1))
      = (∑ i ∈ Finset.range 49, stT215 (i+1)) + stT215 50 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 49
    simpa using h
  have hprev := st215_p49
  have hstep := st215_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p51 : ((5520445799603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT215 (i+1))
      = (∑ i ∈ Finset.range 50, stT215 (i+1)) + stT215 51 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 50
    simpa using h
  have hprev := st215_p50
  have hstep := st215_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p52 : ((9779157588607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT215 (i+1))
      = (∑ i ∈ Finset.range 51, stT215 (i+1)) + stT215 52 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 51
    simpa using h
  have hprev := st215_p51
  have hstep := st215_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p53 : ((10967169322637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT215 (i+1))
      = (∑ i ∈ Finset.range 52, stT215 (i+1)) + stT215 53 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 52
    simpa using h
  have hprev := st215_p52
  have hstep := st215_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p54 : ((10739807623709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT215 (i+1))
      = (∑ i ∈ Finset.range 53, stT215 (i+1)) + stT215 54 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 53
    simpa using h
  have hprev := st215_p53
  have hstep := st215_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p55 : ((9939193775309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT215 (i+1))
      = (∑ i ∈ Finset.range 54, stT215 (i+1)) + stT215 55 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 54
    simpa using h
  have hprev := st215_p54
  have hstep := st215_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p56 : ((11248057395293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT215 (i+1))
      = (∑ i ∈ Finset.range 55, stT215 (i+1)) + stT215 56 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 55
    simpa using h
  have hprev := st215_p55
  have hstep := st215_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p57 : ((1006176457997/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT215 (i+1))
      = (∑ i ∈ Finset.range 56, stT215 (i+1)) + stT215 57 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 56
    simpa using h
  have hprev := st215_p56
  have hstep := st215_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p58 : ((5352550799917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT215 (i+1))
      = (∑ i ∈ Finset.range 57, stT215 (i+1)) + stT215 58 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 57
    simpa using h
  have hprev := st215_p57
  have hstep := st215_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p59 : ((5366585163337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT215 (i+1))
      = (∑ i ∈ Finset.range 58, stT215 (i+1)) + stT215 59 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 58
    simpa using h
  have hprev := st215_p58
  have hstep := st215_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p60 : ((2530373578421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT215 (i+1))
      = (∑ i ∈ Finset.range 59, stT215 (i+1)) + stT215 60 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 59
    simpa using h
  have hprev := st215_p59
  have hstep := st215_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p61 : ((2782234767701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT215 (i+1))
      = (∑ i ∈ Finset.range 60, stT215 (i+1)) + stT215 61 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 60
    simpa using h
  have hprev := st215_p60
  have hstep := st215_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p62 : ((495982666321/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT215 (i+1))
      = (∑ i ∈ Finset.range 61, stT215 (i+1)) + stT215 62 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 61
    simpa using h
  have hprev := st215_p61
  have hstep := st215_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p63 : ((1397422262647/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT215 (i+1))
      = (∑ i ∈ Finset.range 62, stT215 (i+1)) + stT215 63 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 62
    simpa using h
  have hprev := st215_p62
  have hstep := st215_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p64 : ((4981424813977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT215 (i+1))
      = (∑ i ∈ Finset.range 63, stT215 (i+1)) + stT215 64 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 63
    simpa using h
  have hprev := st215_p63
  have hstep := st215_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p65 : ((2773329812153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT215 (i+1))
      = (∑ i ∈ Finset.range 64, stT215 (i+1)) + stT215 65 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 64
    simpa using h
  have hprev := st215_p64
  have hstep := st215_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p66 : ((10053566579027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT215 (i+1))
      = (∑ i ∈ Finset.range 65, stT215 (i+1)) + stT215 66 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 65
    simpa using h
  have hprev := st215_p65
  have hstep := st215_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p67 : ((11021292386919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT215 (i+1))
      = (∑ i ∈ Finset.range 66, stT215 (i+1)) + stT215 67 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 66
    simpa using h
  have hprev := st215_p66
  have hstep := st215_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p68 : ((10093799107349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT215 (i+1))
      = (∑ i ∈ Finset.range 67, stT215 (i+1)) + stT215 68 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 67
    simpa using h
  have hprev := st215_p67
  have hstep := st215_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p69 : ((11016633311261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT215 (i+1))
      = (∑ i ∈ Finset.range 68, stT215 (i+1)) + stT215 69 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 68
    simpa using h
  have hprev := st215_p68
  have hstep := st215_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p70 : ((2012901821789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT215 (i+1))
      = (∑ i ∈ Finset.range 69, stT215 (i+1)) + stT215 70 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 69
    simpa using h
  have hprev := st215_p69
  have hstep := st215_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p71 : ((11071642321851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT215 (i+1))
      = (∑ i ∈ Finset.range 70, stT215 (i+1)) + stT215 71 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 70
    simpa using h
  have hprev := st215_p70
  have hstep := st215_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p72 : ((9996838199339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT215 (i+1))
      = (∑ i ∈ Finset.range 71, stT215 (i+1)) + stT215 72 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 71
    simpa using h
  have hprev := st215_p71
  have hstep := st215_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p73 : ((11131741270421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT215 (i+1))
      = (∑ i ∈ Finset.range 72, stT215 (i+1)) + stT215 73 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 72
    simpa using h
  have hprev := st215_p72
  have hstep := st215_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p74 : ((2492435512117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT215 (i+1))
      = (∑ i ∈ Finset.range 73, stT215 (i+1)) + stT215 74 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 73
    simpa using h
  have hprev := st215_p73
  have hstep := st215_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p75 : ((693450676123/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT215 (i+1))
      = (∑ i ∈ Finset.range 74, stT215 (i+1)) + stT215 75 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 74
    simpa using h
  have hprev := st215_p74
  have hstep := st215_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p76 : ((1262400838823/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT215 (i+1))
      = (∑ i ∈ Finset.range 75, stT215 (i+1)) + stT215 76 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 75
    simpa using h
  have hprev := st215_p75
  have hstep := st215_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p77 : ((10851071365779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT215 (i+1))
      = (∑ i ∈ Finset.range 76, stT215 (i+1)) + stT215 77 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 76
    simpa using h
  have hprev := st215_p76
  have hstep := st215_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p78 : ((10459355262567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT215 (i+1))
      = (∑ i ∈ Finset.range 77, stT215 (i+1)) + stT215 78 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 77
    simpa using h
  have hprev := st215_p77
  have hstep := st215_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p79 : ((10403624028487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT215 (i+1))
      = (∑ i ∈ Finset.range 78, stT215 (i+1)) + stT215 79 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 78
    simpa using h
  have hprev := st215_p78
  have hstep := st215_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p80 : ((10926440856013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT215 (i+1))
      = (∑ i ∈ Finset.range 79, stT215 (i+1)) + stT215 80 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 79
    simpa using h
  have hprev := st215_p79
  have hstep := st215_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p81 : ((2003564914713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT215 (i+1))
      = (∑ i ∈ Finset.range 80, stT215 (i+1)) + stT215 81 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 80
    simpa using h
  have hprev := st215_p80
  have hstep := st215_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p82 : ((277885661067/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT215 (i+1))
      = (∑ i ∈ Finset.range 81, stT215 (i+1)) + stT215 82 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 81
    simpa using h
  have hprev := st215_p81
  have hstep := st215_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p83 : ((1011566026899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT215 (i+1))
      = (∑ i ∈ Finset.range 82, stT215 (i+1)) + stT215 83 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 82
    simpa using h
  have hprev := st215_p82
  have hstep := st215_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p84 : ((5356066219577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT215 (i+1))
      = (∑ i ∈ Finset.range 83, stT215 (i+1)) + stT215 84 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 83
    simpa using h
  have hprev := st215_p83
  have hstep := st215_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p85 : ((5366200123213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT215 (i+1))
      = (∑ i ∈ Finset.range 84, stT215 (i+1)) + stT215 85 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 84
    simpa using h
  have hprev := st215_p84
  have hstep := st215_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p86 : ((5041731228013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT215 (i+1))
      = (∑ i ∈ Finset.range 85, stT215 (i+1)) + stT215 86 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 85
    simpa using h
  have hprev := st215_p85
  have hstep := st215_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p87 : ((5558467233717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT215 (i+1))
      = (∑ i ∈ Finset.range 86, stT215 (i+1)) + stT215 87 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 86
    simpa using h
  have hprev := st215_p86
  have hstep := st215_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p88 : ((5070749616639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT215 (i+1))
      = (∑ i ∈ Finset.range 87, stT215 (i+1)) + stT215 88 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 87
    simpa using h
  have hprev := st215_p87
  have hstep := st215_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p89 : ((1059608530671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT215 (i+1))
      = (∑ i ∈ Finset.range 88, stT215 (i+1)) + stT215 89 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 88
    simpa using h
  have hprev := st215_p88
  have hstep := st215_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p90 : ((5451779863371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT215 (i+1))
      = (∑ i ∈ Finset.range 89, stT215 (i+1)) + stT215 90 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 89
    simpa using h
  have hprev := st215_p89
  have hstep := st215_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p91 : ((2497011053783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT215 (i+1))
      = (∑ i ∈ Finset.range 90, stT215 (i+1)) + stT215 91 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 90
    simpa using h
  have hprev := st215_p90
  have hstep := st215_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p92 : ((2747274728237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT215 (i+1))
      = (∑ i ∈ Finset.range 91, stT215 (i+1)) + stT215 92 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 91
    simpa using h
  have hprev := st215_p91
  have hstep := st215_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p93 : ((525944962513/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT215 (i+1))
      = (∑ i ∈ Finset.range 92, stT215 (i+1)) + stT215 93 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 92
    simpa using h
  have hprev := st215_p92
  have hstep := st215_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p94 : ((1014439507917/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT215 (i+1))
      = (∑ i ∈ Finset.range 93, stT215 (i+1)) + stT215 94 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 93
    simpa using h
  have hprev := st215_p93
  have hstep := st215_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p95 : ((5557010105771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT215 (i+1))
      = (∑ i ∈ Finset.range 94, stT215 (i+1)) + stT215 95 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 94
    simpa using h
  have hprev := st215_p94
  have hstep := st215_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p96 : ((10247858973061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT215 (i+1))
      = (∑ i ∈ Finset.range 95, stT215 (i+1)) + stT215 96 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 95
    simpa using h
  have hprev := st215_p95
  have hstep := st215_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p97 : ((2069787130403/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT215 (i+1))
      = (∑ i ∈ Finset.range 96, stT215 (i+1)) + stT215 97 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 96
    simpa using h
  have hprev := st215_p96
  have hstep := st215_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p98 : ((11098846232863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT215 (i+1))
      = (∑ i ∈ Finset.range 97, stT215 (i+1)) + stT215 98 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 97
    simpa using h
  have hprev := st215_p97
  have hstep := st215_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p99 : ((10119025641321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT215 (i+1))
      = (∑ i ∈ Finset.range 98, stT215 (i+1)) + stT215 99 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 98
    simpa using h
  have hprev := st215_p98
  have hstep := st215_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p100 : ((2095242256827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT215 (i+1))
      = (∑ i ∈ Finset.range 99, stT215 (i+1)) + stT215 100 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 99
    simpa using h
  have hprev := st215_p99
  have hstep := st215_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p101 : ((11067955807887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT215 (i+1))
      = (∑ i ∈ Finset.range 100, stT215 (i+1)) + stT215 101 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 100
    simpa using h
  have hprev := st215_p100
  have hstep := st215_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p102 : ((10081721862931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT215 (i+1))
      = (∑ i ∈ Finset.range 101, stT215 (i+1)) + stT215 102 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 101
    simpa using h
  have hprev := st215_p101
  have hstep := st215_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p103 : ((10498921985479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT215 (i+1))
      = (∑ i ∈ Finset.range 102, stT215 (i+1)) + stT215 103 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 102
    simpa using h
  have hprev := st215_p102
  have hstep := st215_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p104 : ((11074212582199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT215 (i+1))
      = (∑ i ∈ Finset.range 103, stT215 (i+1)) + stT215 104 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 103
    simpa using h
  have hprev := st215_p103
  have hstep := st215_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p105 : ((2021572349877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT215 (i+1))
      = (∑ i ∈ Finset.range 104, stT215 (i+1)) + stT215 105 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 104
    simpa using h
  have hprev := st215_p104
  have hstep := st215_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p106 : ((1041956361773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT215 (i+1))
      = (∑ i ∈ Finset.range 105, stT215 (i+1)) + stT215 106 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 105
    simpa using h
  have hprev := st215_p105
  have hstep := st215_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p107 : ((5555166612849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT215 (i+1))
      = (∑ i ∈ Finset.range 106, stT215 (i+1)) + stT215 107 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 106
    simpa using h
  have hprev := st215_p106
  have hstep := st215_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p108 : ((5106024411587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT215 (i+1))
      = (∑ i ∈ Finset.range 107, stT215 (i+1)) + stT215 108 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 107
    simpa using h
  have hprev := st215_p107
  have hstep := st215_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p109 : ((640880667487/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT215 (i+1))
      = (∑ i ∈ Finset.range 108, stT215 (i+1)) + stT215 109 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 108
    simpa using h
  have hprev := st215_p108
  have hstep := st215_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p110 : ((277951137027/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT215 (i+1))
      = (∑ i ∈ Finset.range 109, stT215 (i+1)) + stT215 110 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 109
    simpa using h
  have hprev := st215_p109
  have hstep := st215_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p111 : ((2607375397443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT215 (i+1))
      = (∑ i ∈ Finset.range 110, stT215 (i+1)) + stT215 111 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 110
    simpa using h
  have hprev := st215_p110
  have hstep := st215_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p112 : ((2514988516467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT215 (i+1))
      = (∑ i ∈ Finset.range 111, stT215 (i+1)) + stT215 112 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 111
    simpa using h
  have hprev := st215_p111
  have hstep := st215_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p113 : ((2749713207987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT215 (i+1))
      = (∑ i ∈ Finset.range 112, stT215 (i+1)) + stT215 113 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 112
    simpa using h
  have hprev := st215_p112
  have hstep := st215_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p114 : ((5378082802107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT215 (i+1))
      = (∑ i ∈ Finset.range 113, stT215 (i+1)) + stT215 114 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 113
    simpa using h
  have hprev := st215_p113
  have hstep := st215_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p115 : ((9970542264279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT215 (i+1))
      = (∑ i ∈ Finset.range 114, stT215 (i+1)) + stT215 115 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 114
    simpa using h
  have hprev := st215_p114
  have hstep := st215_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p116 : ((10673940826263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT215 (i+1))
      = (∑ i ∈ Finset.range 115, stT215 (i+1)) + stT215 116 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 115
    simpa using h
  have hprev := st215_p115
  have hstep := st215_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p117 : ((11064657638763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT215 (i+1))
      = (∑ i ∈ Finset.range 116, stT215 (i+1)) + stT215 117 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 116
    simpa using h
  have hprev := st215_p116
  have hstep := st215_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p118 : ((634905199593/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT215 (i+1))
      = (∑ i ∈ Finset.range 117, stT215 (i+1)) + stT215 118 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 117
    simpa using h
  have hprev := st215_p117
  have hstep := st215_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p119 : ((319344893643/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT215 (i+1))
      = (∑ i ∈ Finset.range 118, stT215 (i+1)) + stT215 119 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 118
    simpa using h
  have hprev := st215_p118
  have hstep := st215_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p120 : ((5546274103263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT215 (i+1))
      = (∑ i ∈ Finset.range 119, stT215 (i+1)) + stT215 120 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 119
    simpa using h
  have hprev := st215_p119
  have hstep := st215_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p121 : ((2130060359733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT215 (i+1))
      = (∑ i ∈ Finset.range 120, stT215 (i+1)) + stT215 121 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 120
    simpa using h
  have hprev := st215_p120
  have hstep := st215_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p122 : ((9961753500357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT215 (i+1))
      = (∑ i ∈ Finset.range 121, stT215 (i+1)) + stT215 122 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 121
    simpa using h
  have hprev := st215_p121
  have hstep := st215_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p123 : ((10662972464967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT215 (i+1))
      = (∑ i ∈ Finset.range 122, stT215 (i+1)) + stT215 123 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 122
    simpa using h
  have hprev := st215_p122
  have hstep := st215_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p124 : ((11101034935923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT215 (i+1))
      = (∑ i ∈ Finset.range 123, stT215 (i+1)) + stT215 124 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 123
    simpa using h
  have hprev := st215_p123
  have hstep := st215_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p125 : ((10261869169903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT215 (i+1))
      = (∑ i ∈ Finset.range 124, stT215 (i+1)) + stT215 125 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 124
    simpa using h
  have hprev := st215_p124
  have hstep := st215_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p126 : ((1007512211827/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT215 (i+1))
      = (∑ i ∈ Finset.range 125, stT215 (i+1)) + stT215 126 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 125
    simpa using h
  have hprev := st215_p125
  have hstep := st215_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p127 : ((5479713694171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT215 (i+1))
      = (∑ i ∈ Finset.range 126, stT215 (i+1)) + stT215 127 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 126
    simpa using h
  have hprev := st215_p126
  have hstep := st215_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p128 : ((5465042545597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT215 (i+1))
      = (∑ i ∈ Finset.range 127, stT215 (i+1)) + stT215 128 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 127
    simpa using h
  have hprev := st215_p127
  have hstep := st215_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p129 : ((5028831902157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT215 (i+1))
      = (∑ i ∈ Finset.range 128, stT215 (i+1)) + stT215 129 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 128
    simpa using h
  have hprev := st215_p128
  have hstep := st215_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p130 : ((2563316539133/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT215 (i+1))
      = (∑ i ∈ Finset.range 129, stT215 (i+1)) + stT215 130 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 129
    simpa using h
  have hprev := st215_p129
  have hstep := st215_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p131 : ((2771866407543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT215 (i+1))
      = (∑ i ∈ Finset.range 130, stT215 (i+1)) + stT215 131 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 130
    simpa using h
  have hprev := st215_p130
  have hstep := st215_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p132 : ((10776018686247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT215 (i+1))
      = (∑ i ∈ Finset.range 131, stT215 (i+1)) + stT215 132 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 131
    simpa using h
  have hprev := st215_p131
  have hstep := st215_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p133 : ((9983428119647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT215 (i+1))
      = (∑ i ∈ Finset.range 132, stT215 (i+1)) + stT215 133 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 132
    simpa using h
  have hprev := st215_p132
  have hstep := st215_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p134 : ((10364906181371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT215 (i+1))
      = (∑ i ∈ Finset.range 133, stT215 (i+1)) + stT215 134 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 133
    simpa using h
  have hprev := st215_p133
  have hstep := st215_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p135 : ((2225242155621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT215 (i+1))
      = (∑ i ∈ Finset.range 134, stT215 (i+1)) + stT215 135 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 134
    simpa using h
  have hprev := st215_p134
  have hstep := st215_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p136 : ((10714257421017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT215 (i+1))
      = (∑ i ∈ Finset.range 135, stT215 (i+1)) + stT215 136 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 135
    simpa using h
  have hprev := st215_p135
  have hstep := st215_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p137 : ((9966662559771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT215 (i+1))
      = (∑ i ∈ Finset.range 136, stT215 (i+1)) + stT215 137 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 136
    simpa using h
  have hprev := st215_p136
  have hstep := st215_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p138 : ((2074680918831/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT215 (i+1))
      = (∑ i ∈ Finset.range 137, stT215 (i+1)) + stT215 138 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 137
    simpa using h
  have hprev := st215_p137
  have hstep := st215_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p139 : ((11125782974051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT215 (i+1))
      = (∑ i ∈ Finset.range 138, stT215 (i+1)) + stT215 139 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 138
    simpa using h
  have hprev := st215_p138
  have hstep := st215_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p140 : ((10757959685881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT215 (i+1))
      = (∑ i ∈ Finset.range 139, stT215 (i+1)) + stT215 140 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 139
    simpa using h
  have hprev := st215_p139
  have hstep := st215_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p141 : ((9985450287673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT215 (i+1))
      = (∑ i ∈ Finset.range 140, stT215 (i+1)) + stT215 141 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 140
    simpa using h
  have hprev := st215_p140
  have hstep := st215_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p142 : ((10279707426961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT215 (i+1))
      = (∑ i ∈ Finset.range 141, stT215 (i+1)) + stT215 142 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 141
    simpa using h
  have hprev := st215_p141
  have hstep := st215_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p143 : ((2215893172197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT215 (i+1))
      = (∑ i ∈ Finset.range 142, stT215 (i+1)) + stT215 143 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 142
    simpa using h
  have hprev := st215_p142
  have hstep := st215_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p144 : ((2178902309271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT215 (i+1))
      = (∑ i ∈ Finset.range 143, stT215 (i+1)) + stT215 144 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 143
    simpa using h
  have hprev := st215_p143
  have hstep := st215_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p145 : ((2014448302167/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT215 (i+1))
      = (∑ i ∈ Finset.range 144, stT215 (i+1)) + stT215 145 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 144
    simpa using h
  have hprev := st215_p144
  have hstep := st215_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p146 : ((505584961721/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT215 (i+1))
      = (∑ i ∈ Finset.range 145, stT215 (i+1)) + stT215 146 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 145
    simpa using h
  have hprev := st215_p145
  have hstep := st215_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p147 : ((5467587324733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT215 (i+1))
      = (∑ i ∈ Finset.range 146, stT215 (i+1)) + stT215 147 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 146
    simpa using h
  have hprev := st215_p146
  have hstep := st215_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p148 : ((1384137641587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT215 (i+1))
      = (∑ i ∈ Finset.range 147, stT215 (i+1)) + stT215 148 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 147
    simpa using h
  have hprev := st215_p147
  have hstep := st215_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p149 : ((257210342211/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT215 (i+1))
      = (∑ i ∈ Finset.range 148, stT215 (i+1)) + stT215 149 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 148
    simpa using h
  have hprev := st215_p148
  have hstep := st215_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p150 : ((1990448292223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT215 (i+1))
      = (∑ i ∈ Finset.range 149, stT215 (i+1)) + stT215 150 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 149
    simpa using h
  have hprev := st215_p149
  have hstep := st215_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p151 : ((10638863693083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT215 (i+1))
      = (∑ i ∈ Finset.range 150, stT215 (i+1)) + stT215 151 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 150
    simpa using h
  have hprev := st215_p150
  have hstep := st215_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p152 : ((11172521810449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT215 (i+1))
      = (∑ i ∈ Finset.range 151, stT215 (i+1)) + stT215 152 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 151
    simpa using h
  have hprev := st215_p151
  have hstep := st215_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p153 : ((5328406842007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT215 (i+1))
      = (∑ i ∈ Finset.range 152, stT215 (i+1)) + stT215 153 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 152
    simpa using h
  have hprev := st215_p152
  have hstep := st215_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p154 : ((4979045503649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT215 (i+1))
      = (∑ i ∈ Finset.range 153, stT215 (i+1)) + stT215 154 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 153
    simpa using h
  have hprev := st215_p153
  have hstep := st215_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p155 : ((2556923669381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT215 (i+1))
      = (∑ i ∈ Finset.range 154, stT215 (i+1)) + stT215 155 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 154
    simpa using h
  have hprev := st215_p154
  have hstep := st215_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p156 : ((2754698762981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT215 (i+1))
      = (∑ i ∈ Finset.range 155, stT215 (i+1)) + stT215 156 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 155
    simpa using h
  have hprev := st215_p155
  have hstep := st215_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p157 : ((276322351859/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT215 (i+1))
      = (∑ i ∈ Finset.range 156, stT215 (i+1)) + stT215 157 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 156
    simpa using h
  have hprev := st215_p156
  have hstep := st215_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p158 : ((5140867521331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT215 (i+1))
      = (∑ i ∈ Finset.range 157, stT215 (i+1)) + stT215 158 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 157
    simpa using h
  have hprev := st215_p157
  have hstep := st215_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p159 : ((4963807163077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT215 (i+1))
      = (∑ i ∈ Finset.range 158, stT215 (i+1)) + stT215 159 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 158
    simpa using h
  have hprev := st215_p158
  have hstep := st215_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p160 : ((5269738392421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT215 (i+1))
      = (∑ i ∈ Finset.range 159, stT215 (i+1)) + stT215 160 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 159
    simpa using h
  have hprev := st215_p159
  have hstep := st215_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p161 : ((5582487236161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT215 (i+1))
      = (∑ i ∈ Finset.range 160, stT215 (i+1)) + stT215 161 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 160
    simpa using h
  have hprev := st215_p160
  have hstep := st215_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p162 : ((10848602791697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT215 (i+1))
      = (∑ i ∈ Finset.range 161, stT215 (i+1)) + stT215 162 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 161
    simpa using h
  have hprev := st215_p161
  have hstep := st215_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p163 : ((2015231411917/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT215 (i+1))
      = (∑ i ∈ Finset.range 162, stT215 (i+1)) + stT215 163 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 162
    simpa using h
  have hprev := st215_p162
  have hstep := st215_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p164 : ((5003302138443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT215 (i+1))
      = (∑ i ∈ Finset.range 163, stT215 (i+1)) + stT215 164 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 163
    simpa using h
  have hprev := st215_p163
  have hstep := st215_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p165 : ((2684268599943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT215 (i+1))
      = (∑ i ∈ Finset.range 164, stT215 (i+1)) + stT215 165 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 164
    simpa using h
  have hprev := st215_p164
  have hstep := st215_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p166 : ((5595469877261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT215 (i+1))
      = (∑ i ∈ Finset.range 165, stT215 (i+1)) + stT215 166 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 165
    simpa using h
  have hprev := st215_p165
  have hstep := st215_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p167 : ((5356198079693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT215 (i+1))
      = (∑ i ∈ Finset.range 166, stT215 (i+1)) + stT215 167 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 166
    simpa using h
  have hprev := st215_p166
  have hstep := st215_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p168 : ((4997857750839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT215 (i+1))
      = (∑ i ∈ Finset.range 167, stT215 (i+1)) + stT215 168 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 167
    simpa using h
  have hprev := st215_p167
  have hstep := st215_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p169 : ((2515172897637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT215 (i+1))
      = (∑ i ∈ Finset.range 168, stT215 (i+1)) + stT215 169 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 168
    simpa using h
  have hprev := st215_p168
  have hstep := st215_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p170 : ((540475384419/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT215 (i+1))
      = (∑ i ∈ Finset.range 169, stT215 (i+1)) + stT215 170 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 169
    simpa using h
  have hprev := st215_p169
  have hstep := st215_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p171 : ((559721832211/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT215 (i+1))
      = (∑ i ∈ Finset.range 170, stT215 (i+1)) + stT215 171 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 170
    simpa using h
  have hprev := st215_p170
  have hstep := st215_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p172 : ((10688132904797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT215 (i+1))
      = (∑ i ∈ Finset.range 171, stT215 (i+1)) + stT215 172 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 171
    simpa using h
  have hprev := st215_p171
  have hstep := st215_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p173 : ((9988324614953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT215 (i+1))
      = (∑ i ∈ Finset.range 172, stT215 (i+1)) + stT215 173 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 172
    simpa using h
  have hprev := st215_p172
  have hstep := st215_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p174 : ((10041372522503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT215 (i+1))
      = (∑ i ∈ Finset.range 173, stT215 (i+1)) + stT215 174 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 173
    simpa using h
  have hprev := st215_p173
  have hstep := st215_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p175 : ((10770155148023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT215 (i+1))
      = (∑ i ∈ Finset.range 174, stT215 (i+1)) + stT215 175 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 174
    simpa using h
  have hprev := st215_p174
  have hstep := st215_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p176 : ((2240921884021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT215 (i+1))
      = (∑ i ∈ Finset.range 175, stT215 (i+1)) + stT215 176 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 175
    simpa using h
  have hprev := st215_p175
  have hstep := st215_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p177 : ((84201569941/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT215 (i+1))
      = (∑ i ∈ Finset.range 176, stT215 (i+1)) + stT215 177 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 176
    simpa using h
  have hprev := st215_p176
  have hstep := st215_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p178 : ((1256310447733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT215 (i+1))
      = (∑ i ∈ Finset.range 177, stT215 (i+1)) + stT215 178 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 177
    simpa using h
  have hprev := st215_p177
  have hstep := st215_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p179 : ((2489866888177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT215 (i+1))
      = (∑ i ∈ Finset.range 178, stT215 (i+1)) + stT215 179 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 178
    simpa using h
  have hprev := st215_p178
  have hstep := st215_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p180 : ((10615300199723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT215 (i+1))
      = (∑ i ∈ Finset.range 179, stT215 (i+1)) + stT215 180 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 179
    simpa using h
  have hprev := st215_p179
  have hstep := st215_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p181 : ((11185634888981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT215 (i+1))
      = (∑ i ∈ Finset.range 180, stT215 (i+1)) + stT215 181 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 180
    simpa using h
  have hprev := st215_p180
  have hstep := st215_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p182 : ((10959575135231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT215 (i+1))
      = (∑ i ∈ Finset.range 181, stT215 (i+1)) + stT215 182 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 181
    simpa using h
  have hprev := st215_p181
  have hstep := st215_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p183 : ((10222851705591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT215 (i+1))
      = (∑ i ∈ Finset.range 182, stT215 (i+1)) + stT215 183 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 182
    simpa using h
  have hprev := st215_p182
  have hstep := st215_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p184 : ((9881092207741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT215 (i+1))
      = (∑ i ∈ Finset.range 183, stT215 (i+1)) + stT215 184 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 183
    simpa using h
  have hprev := st215_p183
  have hstep := st215_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p185 : ((10345260008859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT215 (i+1))
      = (∑ i ∈ Finset.range 184, stT215 (i+1)) + stT215 185 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 184
    simpa using h
  have hprev := st215_p184
  have hstep := st215_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p186 : ((11051586750829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT215 (i+1))
      = (∑ i ∈ Finset.range 185, stT215 (i+1)) + stT215 186 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 185
    simpa using h
  have hprev := st215_p185
  have hstep := st215_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p187 : ((11158225952773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT215 (i+1))
      = (∑ i ∈ Finset.range 186, stT215 (i+1)) + stT215 187 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 186
    simpa using h
  have hprev := st215_p186
  have hstep := st215_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p188 : ((2636095385987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT215 (i+1))
      = (∑ i ∈ Finset.range 187, stT215 (i+1)) + stT215 188 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 187
    simpa using h
  have hprev := st215_p187
  have hstep := st215_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p189 : ((4965988142087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT215 (i+1))
      = (∑ i ∈ Finset.range 188, stT215 (i+1)) + stT215 189 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 188
    simpa using h
  have hprev := st215_p188
  have hstep := st215_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p190 : ((5014366509147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT215 (i+1))
      = (∑ i ∈ Finset.range 189, stT215 (i+1)) + stT215 190 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 189
    simpa using h
  have hprev := st215_p189
  have hstep := st215_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p191 : ((1071814274831/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT215 (i+1))
      = (∑ i ∈ Finset.range 190, stT215 (i+1)) + stT215 191 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 190
    simpa using h
  have hprev := st215_p190
  have hstep := st215_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p192 : ((560671465977/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT215 (i+1))
      = (∑ i ∈ Finset.range 191, stT215 (i+1)) + stT215 192 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 191
    simpa using h
  have hprev := st215_p191
  have hstep := st215_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p193 : ((2739881435649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT215 (i+1))
      = (∑ i ∈ Finset.range 192, stT215 (i+1)) + stT215 193 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 192
    simpa using h
  have hprev := st215_p192
  have hstep := st215_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p194 : ((5122531601463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT215 (i+1))
      = (∑ i ∈ Finset.range 193, stT215 (i+1)) + stT215 194 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 193
    simpa using h
  have hprev := st215_p193
  have hstep := st215_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p195 : ((9861829247871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT215 (i+1))
      = (∑ i ∈ Finset.range 194, stT215 (i+1)) + stT215 195 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 194
    simpa using h
  have hprev := st215_p194
  have hstep := st215_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p196 : ((10226034597951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT215 (i+1))
      = (∑ i ∈ Finset.range 195, stT215 (i+1)) + stT215 196 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 195
    simpa using h
  have hprev := st215_p195
  have hstep := st215_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p197 : ((10937251363221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT215 (i+1))
      = (∑ i ∈ Finset.range 196, stT215 (i+1)) + stT215 197 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 196
    simpa using h
  have hprev := st215_p196
  have hstep := st215_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p198 : ((2807351669613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT215 (i+1))
      = (∑ i ∈ Finset.range 197, stT215 (i+1)) + stT215 198 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 197
    simpa using h
  have hprev := st215_p197
  have hstep := st215_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p199 : ((5397536275203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT215 (i+1))
      = (∑ i ∈ Finset.range 198, stT215 (i+1)) + stT215 199 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 198
    simpa using h
  have hprev := st215_p198
  have hstep := st215_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p200 : ((2019537230067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT215 (i+1))
      = (∑ i ∈ Finset.range 199, stT215 (i+1)) + stT215 200 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 199
    simpa using h
  have hprev := st215_p199
  have hstep := st215_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p201 : ((9867648837971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT215 (i+1))
      = (∑ i ∈ Finset.range 200, stT215 (i+1)) + stT215 201 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 200
    simpa using h
  have hprev := st215_p200
  have hstep := st215_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p202 : ((2584835946189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT215 (i+1))
      = (∑ i ∈ Finset.range 201, stT215 (i+1)) + stT215 202 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 201
    simpa using h
  have hprev := st215_p201
  have hstep := st215_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p203 : ((1377920030193/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT215 (i+1))
      = (∑ i ∈ Finset.range 202, stT215 (i+1)) + stT215 203 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 202
    simpa using h
  have hprev := st215_p202
  have hstep := st215_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p204 : ((2805635592501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT215 (i+1))
      = (∑ i ∈ Finset.range 203, stT215 (i+1)) + stT215 204 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 203
    simpa using h
  have hprev := st215_p203
  have hstep := st215_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p205 : ((2684978843527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT215 (i+1))
      = (∑ i ∈ Finset.range 204, stT215 (i+1)) + stT215 205 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 204
    simpa using h
  have hprev := st215_p204
  have hstep := st215_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p206 : ((2515707318227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT215 (i+1))
      = (∑ i ∈ Finset.range 205, stT215 (i+1)) + stT215 206 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 205
    simpa using h
  have hprev := st215_p205
  have hstep := st215_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p207 : ((9863127099179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT215 (i+1))
      = (∑ i ∈ Finset.range 206, stT215 (i+1)) + stT215 207 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 206
    simpa using h
  have hprev := st215_p206
  have hstep := st215_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p208 : ((645816592019/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT215 (i+1))
      = (∑ i ∈ Finset.range 207, stT215 (i+1)) + stT215 208 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 207
    simpa using h
  have hprev := st215_p207
  have hstep := st215_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p209 : ((2752559565149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT215 (i+1))
      = (∑ i ∈ Finset.range 208, stT215 (i+1)) + stT215 209 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 208
    simpa using h
  have hprev := st215_p208
  have hstep := st215_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p210 : ((5619963197923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT215 (i+1))
      = (∑ i ∈ Finset.range 209, stT215 (i+1)) + stT215 210 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 209
    simpa using h
  have hprev := st215_p209
  have hstep := st215_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p211 : ((337685691597/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT215 (i+1))
      = (∑ i ∈ Finset.range 210, stT215 (i+1)) + stT215 211 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 210
    simpa using h
  have hprev := st215_p210
  have hstep := st215_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p212 : ((10124701548601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT215 (i+1))
      = (∑ i ∈ Finset.range 211, stT215 (i+1)) + stT215 212 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 211
    simpa using h
  have hprev := st215_p211
  have hstep := st215_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p213 : ((9607650689/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT215 (i+1))
      = (∑ i ∈ Finset.range 212, stT215 (i+1)) + stT215 213 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 212
    simpa using h
  have hprev := st215_p212
  have hstep := st215_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p214 : ((2552597912809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT215 (i+1))
      = (∑ i ∈ Finset.range 213, stT215 (i+1)) + stT215 214 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 213
    simpa using h
  have hprev := st215_p213
  have hstep := st215_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p215 : ((5446166568849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT215 (i+1))
      = (∑ i ∈ Finset.range 214, stT215 (i+1)) + stT215 215 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 214
    simpa using h
  have hprev := st215_p214
  have hstep := st215_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p216 : ((11257073289239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT215 (i+1))
      = (∑ i ∈ Finset.range 215, stT215 (i+1)) + stT215 216 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 215
    simpa using h
  have hprev := st215_p215
  have hstep := st215_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p217 : ((2743937434641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT215 (i+1))
      = (∑ i ∈ Finset.range 216, stT215 (i+1)) + stT215 217 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 216
    simpa using h
  have hprev := st215_p216
  have hstep := st215_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p218 : ((8051995779/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT215 (i+1))
      = (∑ i ∈ Finset.range 217, stT215 (i+1)) + stT215 218 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 217
    simpa using h
  have hprev := st215_p217
  have hstep := st215_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p219 : ((615622232973/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT215 (i+1))
      = (∑ i ∈ Finset.range 218, stT215 (i+1)) + stT215 219 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 218
    simpa using h
  have hprev := st215_p218
  have hstep := st215_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p220 : ((2502159475251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT215 (i+1))
      = (∑ i ∈ Finset.range 219, stT215 (i+1)) + stT215 220 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 219
    simpa using h
  have hprev := st215_p219
  have hstep := st215_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p221 : ((2659652170611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT215 (i+1))
      = (∑ i ∈ Finset.range 220, stT215 (i+1)) + stT215 221 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 220
    simpa using h
  have hprev := st215_p220
  have hstep := st215_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p222 : ((279692555297/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT215 (i+1))
      = (∑ i ∈ Finset.range 221, stT215 (i+1)) + stT215 222 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 221
    simpa using h
  have hprev := st215_p221
  have hstep := st215_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p223 : ((1118227469863/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT215 (i+1))
      = (∑ i ∈ Finset.range 222, stT215 (i+1)) + stT215 223 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 222
    simpa using h
  have hprev := st215_p222
  have hstep := st215_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p224 : ((5315539860011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT215 (i+1))
      = (∑ i ∈ Finset.range 223, stT215 (i+1)) + stT215 224 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 223
    simpa using h
  have hprev := st215_p223
  have hstep := st215_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p225 : ((5003198370507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT215 (i+1))
      = (∑ i ∈ Finset.range 224, stT215 (i+1)) + stT215 225 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 224
    simpa using h
  have hprev := st215_p224
  have hstep := st215_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p226 : ((9835073473009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT215 (i+1))
      = (∑ i ∈ Finset.range 225, stT215 (i+1)) + stT215 226 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 225
    simpa using h
  have hprev := st215_p225
  have hstep := st215_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p227 : ((5128454299583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT215 (i+1))
      = (∑ i ∈ Finset.range 226, stT215 (i+1)) + stT215 227 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 226
    simpa using h
  have hprev := st215_p226
  have hstep := st215_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p228 : ((2729456390831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT215 (i+1))
      = (∑ i ∈ Finset.range 227, stT215 (i+1)) + stT215 228 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 227
    simpa using h
  have hprev := st215_p227
  have hstep := st215_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p229 : ((352269294559/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT215 (i+1))
      = (∑ i ∈ Finset.range 228, stT215 (i+1)) + stT215 229 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 228
    simpa using h
  have hprev := st215_p228
  have hstep := st215_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p230 : ((11034139758999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT215 (i+1))
      = (∑ i ∈ Finset.range 229, stT215 (i+1)) + stT215 230 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 229
    simpa using h
  have hprev := st215_p229
  have hstep := st215_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p231 : ((10399648353463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT215 (i+1))
      = (∑ i ∈ Finset.range 230, stT215 (i+1)) + stT215 231 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 230
    simpa using h
  have hprev := st215_p230
  have hstep := st215_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p232 : ((308788505321/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT215 (i+1))
      = (∑ i ∈ Finset.range 231, stT215 (i+1)) + stT215 232 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 231
    simpa using h
  have hprev := st215_p231
  have hstep := st215_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p233 : ((9890775317879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT215 (i+1))
      = (∑ i ∈ Finset.range 232, stT215 (i+1)) + stT215 233 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 232
    simpa using h
  have hprev := st215_p232
  have hstep := st215_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p234 : ((10416880021799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT215 (i+1))
      = (∑ i ∈ Finset.range 233, stT215 (i+1)) + stT215 234 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 233
    simpa using h
  have hprev := st215_p233
  have hstep := st215_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p235 : ((11043508907911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT215 (i+1))
      = (∑ i ∈ Finset.range 234, stT215 (i+1)) + stT215 235 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 234
    simpa using h
  have hprev := st215_p234
  have hstep := st215_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p236 : ((11282743195847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT215 (i+1))
      = (∑ i ∈ Finset.range 235, stT215 (i+1)) + stT215 236 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 235
    simpa using h
  have hprev := st215_p235
  have hstep := st215_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p237 : ((10952824644137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT215 (i+1))
      = (∑ i ∈ Finset.range 236, stT215 (i+1)) + stT215 237 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 236
    simpa using h
  have hprev := st215_p236
  have hstep := st215_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p238 : ((10310299559381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT215 (i+1))
      = (∑ i ∈ Finset.range 237, stT215 (i+1)) + stT215 238 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 237
    simpa using h
  have hprev := st215_p237
  have hstep := st215_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p239 : ((4922635127341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT215 (i+1))
      = (∑ i ∈ Finset.range 238, stT215 (i+1)) + stT215 239 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 238
    simpa using h
  have hprev := st215_p238
  have hstep := st215_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p240 : ((9906815166147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT215 (i+1))
      = (∑ i ∈ Finset.range 239, stT215 (i+1)) + stT215 240 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 239
    simpa using h
  have hprev := st215_p239
  have hstep := st215_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p241 : ((10445140844439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT215 (i+1))
      = (∑ i ∈ Finset.range 240, stT215 (i+1)) + stT215 241 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 240
    simpa using h
  have hprev := st215_p240
  have hstep := st215_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p242 : ((11057490487071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT215 (i+1))
      = (∑ i ∈ Finset.range 241, stT215 (i+1)) + stT215 242 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 241
    simpa using h
  have hprev := st215_p241
  have hstep := st215_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p243 : ((11292550841571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT215 (i+1))
      = (∑ i ∈ Finset.range 242, stT215 (i+1)) + stT215 243 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 242
    simpa using h
  have hprev := st215_p242
  have hstep := st215_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p244 : ((10981254483471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT215 (i+1))
      = (∑ i ∈ Finset.range 243, stT215 (i+1)) + stT215 244 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 243
    simpa using h
  have hprev := st215_p243
  have hstep := st215_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p245 : ((103530959229/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT215 (i+1))
      = (∑ i ∈ Finset.range 244, stT215 (i+1)) + stT215 245 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 244
    simpa using h
  have hprev := st215_p244
  have hstep := st215_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p246 : ((9862172471709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT215 (i+1))
      = (∑ i ∈ Finset.range 245, stT215 (i+1)) + stT215 246 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 245
    simpa using h
  have hprev := st215_p245
  have hstep := st215_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p247 : ((9857989534119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT215 (i+1))
      = (∑ i ∈ Finset.range 246, stT215 (i+1)) + stT215 247 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 246
    simpa using h
  have hprev := st215_p246
  have hstep := st215_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p248 : ((10340082169119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT215 (i+1))
      = (∑ i ∈ Finset.range 247, stT215 (i+1)) + stT215 248 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 247
    simpa using h
  have hprev := st215_p247
  have hstep := st215_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p249 : ((10966025305847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT215 (i+1))
      = (∑ i ∈ Finset.range 248, stT215 (i+1)) + stT215 249 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 248
    simpa using h
  have hprev := st215_p248
  have hstep := st215_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_p250 : ((11297921246017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT215 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT215 (i+1))
      = (∑ i ∈ Finset.range 249, stT215 (i+1)) + stT215 250 := by
    have h := Finset.sum_range_succ (fun i => stT215 (i+1)) 249
    simpa using h
  have hprev := st215_p249
  have hstep := st215_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st215_s250 :
    |Real.sin (((215 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))
      - ((851211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 63643/250000) (δ := 2189/200000000) (ψ := -1426207/1000000) 215 189
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 215`** (evaluated boundary). -/
theorem station_215_sign : hardyG ((((215:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 215 250 (by norm_num) (by norm_num)
    ((-1426207/1000000 : ℚ) : ℝ)
  have hchain := st215_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT215 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((215 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-1426207/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st215_c250
  have hsinb := abs_le.mp st215_s250
  have hbdy_lo : ((-452807742827/7222695312500 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((215 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ))) / 2
          - ((((215:ℕ)):ℝ))
            * Real.sin (((215 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1426207/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((215:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((215:ℝ) * Real.log (250:ℝ) - ((-1426207/1000000 : ℚ) : ℝ))) / 2
        - ((215:ℝ)) * Real.sin ((215:ℝ) * Real.log (250:ℝ) - ((-1426207/1000000 : ℚ) : ℝ))
        ≥ ((-5727611/31250 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((215:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-5727611/31250 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-5727611/31250 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-5727611/31250 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((215:ℕ)):ℝ))+1) * (((((215:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((80132886713/78125000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((11297921246017/10000000000000 : ℚ) : ℝ) + ((-452807742827/7222695312500 : ℚ) : ℝ)
      - ((80132886713/78125000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-1426207/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((215:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-1426207/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((215:ℕ)):ℝ)))).re
      - Real.sin ((-1426207/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((215:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((215:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((215:ℕ)):ℝ))
      = (((((215:ℕ)):ℝ)) * (Real.log ((((215:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((215:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_215
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
  have hθwin : |(((-1426207/1000000 : ℚ) : ℝ) + ((44:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((215:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((215:ℕ)):ℝ)))
    (φ := ((-1426207/1000000 : ℚ) : ℝ) + ((44:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-1426207/1000000 : ℚ) : ℝ) + ((44:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-1426207/1000000 : ℚ)) : ℝ) - Real.pi) + ((44:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-1426207/1000000 : ℚ)) : ℝ) - Real.pi) 44).1,
    (cos_sin_shift ((((-1426207/1000000 : ℚ)) : ℝ) - Real.pi) 44).2]
  exact cos_sin_flip ((-1426207/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_215_sign
end AxiomAudit
