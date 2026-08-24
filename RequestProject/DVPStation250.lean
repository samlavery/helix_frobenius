import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 250` (rung-262.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT250 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((250 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-540941/500000 : ℚ) : ℝ))

theorem st250_c1 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((117417/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 540941/2000000) (δ := 1/1000000000) (ψ := -540941/500000) 250 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t1 : ((234809/500000 : ℚ) : ℝ) ≤ stT250 1 := by
  have hc : ((234809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234809/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((234809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c2 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((10277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1950649/5000000) (δ := 63/5000000) (ψ := -540941/500000) 250 28
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t2 : ((72315802209/10000000000000 : ℚ) : ℝ) ≤ stT250 2 := by
  have hc : ((10227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72315802209/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((10227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c3 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((748361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1813023/10000000) (δ := 6343/500000000) (ψ := -540941/500000) 250 44
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t3 : ((2160187527561/5000000000000 : ℚ) : ℝ) ≤ stT250 3 := by
  have hc : ((748311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2160187527561/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((748311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c4 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-121931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2600347/5000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 55
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t4 : ((-1219435243887/5000000000000 : ℚ) : ℝ) ≤ stT250 4 := by
  have hc : ((-243887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1219435243887/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-243887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c5 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((250587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131751/400000) (δ := 12661/1000000000) (ψ := -540941/500000) 250 64
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t5 : ((224087057299/2000000000000 : ℚ) : ℝ) ≤ stT250 5 := by
  have hc : ((250537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224087057299/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((250537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c6 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-974569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7288969/10000000) (δ := 787/62500000) (ψ := -540941/500000) 250 71
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t6 : ((-3978865498977/10000000000000 : ℚ) : ℝ) ≤ stT250 6 := by
  have hc : ((-974619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3978865498977/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-974619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c7 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-40909/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3161293/5000000) (δ := 6281/500000000) (ψ := -540941/500000) 250 78
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t7 : ((-61852378567/200000000000 : ℚ) : ℝ) ≤ stT250 7 := by
  have hc : ((-81823/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61852378567/200000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-81823/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c8 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((211533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1405277/10000000) (δ := 12697/1000000000) (ψ := -540941/500000) 250 83
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t8 : ((1495675415853/5000000000000 : ℚ) : ℝ) ≤ stT250 8 := by
  have hc : ((423041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1495675415853/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((423041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c9 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-410023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6330719/10000000) (δ := 1257/100000000) (ψ := -540941/500000) 250 88
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t9 : ((-10678335469/39062500000 : ℚ) : ℝ) ≤ stT250 9 := by
  have hc : ((-12814/15625 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10678335469/39062500000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-12814/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c10 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((121711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3312259/10000000) (δ := 6331/500000000) (ψ := -540941/500000) 250 92
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t10 : ((192402419511/2500000000000 : ℚ) : ℝ) ≤ stT250 10 := by
  have hc : ((60843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192402419511/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((60843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c11 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-218003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6575237/10000000) (δ := 12691/1000000000) (ψ := -540941/500000) 250 96
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t11 : ((-657341586267/2500000000000 : ℚ) : ℝ) ≤ stT250 11 := by
  have hc : ((-436031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657341586267/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-436031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c12 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((962913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341499/5000000) (δ := 3153/250000000) (ψ := -540941/500000) 250 99
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t12 : ((2779545728113/10000000000000 : ℚ) : ℝ) ≤ stT250 12 := by
  have hc : ((962863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2779545728113/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((962863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c13 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((27211/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717159/2000000) (δ := 12669/1000000000) (ψ := -540941/500000) 250 102
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t13 : ((150883947/4000000000 : ℚ) : ℝ) ≤ stT250 13 := by
  have hc : ((27201/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150883947/4000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((27201/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c14 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((221541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389703/5000000) (δ := 2531/200000000) (ψ := -540941/500000) 250 105
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t14 : ((37001644987/312500000000 : ℚ) : ℝ) ≤ stT250 14 := by
  have hc : ((55379/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37001644987/312500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((55379/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c15 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((110317/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -611961/5000000) (δ := 6313/500000000) (ψ := -540941/500000) 250 108
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t15 : ((284821032771/1250000000000 : ℚ) : ℝ) ≤ stT250 15 := by
  have hc : ((441243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284821032771/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((441243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c16 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-499011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3848357/5000000) (δ := 3153/250000000) (ψ := -540941/500000) 250 110
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t16 : ((-311897624759/1250000000000 : ℚ) : ℝ) ≤ stT250 16 := by
  have hc : ((-124759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311897624759/1250000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-124759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c17 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((163387/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536801/10000000) (δ := 1269/100000000) (ψ := -540941/500000) 250 113
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t17 : ((99061846803/500000000000 : ℚ) : ℝ) ≤ stT250 17 := by
  have hc : ((163377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99061846803/500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((163377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c18 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((111499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2771273/10000000) (δ := 12527/1000000000) (ψ := -540941/500000) 250 115
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t18 : ((262776133203/2500000000000 : ℚ) : ℝ) ≤ stT250 18 := by
  have hc : ((222973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262776133203/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((222973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c19 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-234493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2573673/5000000) (δ := 12661/1000000000) (ψ := -540941/500000) 250 117
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t19 : ((-134505336461/1250000000000 : ℚ) : ℝ) ≤ stT250 19 := by
  have hc : ((-117259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134505336461/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-117259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c20 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-678043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1447433/2500000) (δ := 12647/1000000000) (ψ := -540941/500000) 250 119
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t20 : ((-379065514581/2500000000000 : ℚ) : ℝ) ≤ stT250 20 := by
  have hc : ((-678093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379065514581/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-678093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c21 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-18373/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4867681/10000000) (δ := 1257/100000000) (ψ := -540941/500000) 250 121
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t21 : ((-80197260429/1000000000000 : ℚ) : ℝ) ≤ stT250 21 := by
  have hc : ((-36751/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80197260429/1000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-36751/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c22 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((265633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263377/5000000) (δ := 6309/500000000) (ψ := -540941/500000) 250 123
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t22 : ((70784764407/625000000000 : ℚ) : ℝ) ≤ stT250 22 := by
  have hc : ((33201/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70784764407/625000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((33201/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c23 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((90359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1106797/10000000) (δ := 12599/1000000000) (ψ := -540941/500000) 250 125
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t23 : ((11775068811/62500000000 : ℚ) : ℝ) ≤ stT250 23 := by
  have hc : ((45177/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11775068811/62500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((45177/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c24 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-179059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2961487/5000000) (δ := 1259/100000000) (ψ := -540941/500000) 250 127
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t24 : ((-365528266803/2500000000000 : ℚ) : ℝ) ≤ stT250 24 := by
  have hc : ((-358143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365528266803/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-358143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c25 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((1767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3882813/10000000) (δ := 313/25000000) (ψ := -540941/500000) 250 128
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t25 : ((881/250000 : ℚ) : ℝ) ≤ stT250 25 := by
  have hc : ((881/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881/250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((881/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c26 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((44353/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188761/625000) (δ := 2507/200000000) (ψ := -540941/500000) 250 130
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t26 : ((347884466307/5000000000000 : ℚ) : ℝ) ≤ stT250 26 := by
  have hc : ((177387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347884466307/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((177387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c27 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-22777/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1214887/2500000) (δ := 12561/1000000000) (ψ := -540941/500000) 250 131
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t27 : ((-350722986741/5000000000000 : ℚ) : ℝ) ≤ stT250 27 := by
  have hc : ((-182241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350722986741/5000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-182241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c28 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((40159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1913283/5000000) (δ := 12547/1000000000) (ψ := -540941/500000) 250 133
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t28 : ((37899435299/5000000000000 : ℚ) : ℝ) ≤ stT250 28 := by
  have hc : ((40109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37899435299/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((40109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c29 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((71791/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2397533/10000000) (δ := 12639/1000000000) (ψ := -540941/500000) 250 134
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t29 : ((533203627467/5000000000000 : ℚ) : ℝ) ≤ stT250 29 := by
  have hc : ((287139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((533203627467/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((287139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c30 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-499977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957489/2500000) (δ := 101/8000000) (ψ := -540941/500000) 250 136
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t30 : ((-228218662871/1250000000000 : ℚ) : ℝ) ≤ stT250 30 := by
  have hc : ((-250001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228218662871/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-250001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c31 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((86453/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3044231/10000000) (δ := 2537/200000000) (ψ := -540941/500000) 250 137
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t31 : ((310503438693/5000000000000 : ℚ) : ℝ) ≤ stT250 31 := by
  have hc : ((172881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310503438693/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((172881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c32 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((906323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1090743/10000000) (δ := 787/62500000) (ψ := -540941/500000) 250 138
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t32 : ((801039298059/5000000000000 : ℚ) : ℝ) ≤ stT250 32 := by
  have hc : ((906273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((801039298059/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((906273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c33 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-135877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461503/1000000) (δ := 12699/1000000000) (ψ := -540941/500000) 250 139
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t33 : ((-118287537927/2500000000000 : ℚ) : ℝ) ≤ stT250 33 := by
  have hc : ((-67951/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118287537927/2500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-67951/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c34 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-198667/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7565191/10000000) (δ := 3149/250000000) (ψ := -540941/500000) 250 140
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t34 : ((-170364136761/1000000000000 : ℚ) : ℝ) ≤ stT250 34 := by
  have hc : ((-198677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170364136761/1000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-198677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c35 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-330677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1433387/2500000) (δ := 6291/500000000) (ψ := -540941/500000) 250 142
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t35 : ((-279494283459/2500000000000 : ℚ) : ℝ) ≤ stT250 35 := by
  have hc : ((-165351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279494283459/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-165351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c36 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((9227/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3834699/10000000) (δ := 507/40000000) (ψ := -540941/500000) 250 143
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t36 : ((15357493857/2500000000000 : ℚ) : ℝ) ≤ stT250 36 := by
  have hc : ((18429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15357493857/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((18429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c37 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((70939/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2418287/10000000) (δ := 1571/125000000) (ψ := -540941/500000) 250 144
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t37 : ((466450642959/5000000000000 : ℚ) : ℝ) ≤ stT250 37 := by
  have hc : ((283731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466450642959/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((283731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c38 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((834567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11669/80000) (δ := 12543/1000000000) (ψ := -540941/500000) 250 145
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t38 : ((676882580319/5000000000000 : ℚ) : ℝ) ≤ stT250 38 := by
  have hc : ((834517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((676882580319/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((834517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c39 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((465663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -931901/10000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 146
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t39 : ((372808641139/2500000000000 : ℚ) : ℝ) ≤ stT250 39 := by
  have hc : ((232819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372808641139/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((232819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c40 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((236793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -816239/10000000) (δ := 12557/1000000000) (ψ := -540941/500000) 250 147
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t40 : ((374382646209/2500000000000 : ℚ) : ℝ) ≤ stT250 40 := by
  have hc : ((473561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374382646209/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((473561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c41 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((56639/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1091327/10000000) (δ := 1583/125000000) (ψ := -540941/500000) 250 148
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t41 : ((707602732119/5000000000000 : ℚ) : ℝ) ≤ stT250 41 := by
  have hc : ((453087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707602732119/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((453087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c42 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((767851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1738291/10000000) (δ := 1579/125000000) (ψ := -540941/500000) 250 149
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t42 : ((1184742280433/10000000000000 : ℚ) : ℝ) ≤ stT250 42 := by
  have hc : ((767801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1184742280433/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((767801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c43 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((457267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2739691/10000000) (δ := 6339/500000000) (ψ := -540941/500000) 250 150
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t43 : ((139449813349/2000000000000 : ℚ) : ℝ) ≤ stT250 43 := by
  have hc : ((457217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139449813349/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((457217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c44 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-60853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4079217/10000000) (δ := 6293/500000000) (ψ := -540941/500000) 250 151
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t44 : ((-91814743971/10000000000000 : ℚ) : ℝ) ≤ stT250 44 := by
  have hc : ((-60903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91814743971/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-60903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c45 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-663791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71771/125000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 152
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t45 : ((-123699468099/1250000000000 : ℚ) : ℝ) ≤ stT250 45 := by
  have hc : ((-663841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123699468099/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-663841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c46 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-998407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7712831/10000000) (δ := 63/5000000) (ψ := -540941/500000) 250 153
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t46 : ((-73607248497/500000000000 : ℚ) : ℝ) ≤ stT250 46 := by
  have hc : ((-998457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73607248497/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-998457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c47 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-65987/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2864303/5000000) (δ := 12603/1000000000) (ψ := -540941/500000) 250 153
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t47 : ((-240648077/2500000000 : ℚ) : ℝ) ≤ stT250 47 := by
  have hc : ((-8249/12500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240648077/2500000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-8249/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c48 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((58949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1589509/5000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 154
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t48 : ((680568633/16000000000 : ℚ) : ℝ) ≤ stT250 48 := by
  have hc : ((58939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680568633/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((58939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c49 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((989761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71611/2000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 155
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t49 : ((1413872432981/10000000000000 : ℚ) : ℝ) ≤ stT250 49 := by
  have hc : ((989711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1413872432981/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((989711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c50 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((231569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2723159/10000000) (δ := 12681/1000000000) (ψ := -540941/500000) 250 156
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t50 : ((40931566859/625000000000 : ℚ) : ℝ) ≤ stT250 50 := by
  have hc : ((28943/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40931566859/625000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((28943/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c51 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-375971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6054497/10000000) (δ := 6287/500000000) (ψ := -540941/500000) 250 157
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t51 : ((-131625013719/1250000000000 : ℚ) : ℝ) ≤ stT250 51 := by
  have hc : ((-93999/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131625013719/1250000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-93999/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c52 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-7591/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760227/1250000) (δ := 12629/1000000000) (ψ := -540941/500000) 250 157
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t52 : ((-21055040433/200000000000 : ℚ) : ℝ) ≤ stT250 52 := by
  have hc : ((-15183/20000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21055040433/200000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-15183/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c53 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((612489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2278977/10000000) (δ := 12667/1000000000) (ψ := -540941/500000) 250 158
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t53 : ((168249854519/2000000000000 : ℚ) : ℝ) ≤ stT250 53 := by
  have hc : ((612439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168249854519/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((612439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c54 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((765763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1746423/10000000) (δ := 12643/1000000000) (ψ := -540941/500000) 250 159
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t54 : ((1042002924651/10000000000000 : ℚ) : ℝ) ≤ stT250 54 := by
  have hc : ((765713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1042002924651/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((765713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c55 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-366827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5986199/10000000) (δ := 251/20000000) (ψ := -540941/500000) 250 160
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t55 : ((-309164523/3125000000 : ℚ) : ℝ) ≤ stT250 55 := by
  have hc : ((-91713/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309164523/3125000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-91713/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c56 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-513577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5275363/10000000) (δ := 12653/1000000000) (ψ := -540941/500000) 250 160
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t56 : ((-686363355489/10000000000000 : ℚ) : ℝ) ≤ stT250 56 := by
  have hc : ((-513627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-686363355489/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-513627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c57 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((968451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12593/200000) (δ := 6273/500000000) (ψ := -540941/500000) 250 161
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t57 : ((320669528333/2500000000000 : ℚ) : ℝ) ≤ stT250 57 := by
  have hc : ((968401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320669528333/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((968401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c58 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-112341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2104219/5000000) (δ := 2513/200000000) (ψ := -540941/500000) 250 162
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t58 : ((-29515337683/2000000000000 : ℚ) : ℝ) ≤ stT250 58 := by
  have hc : ((-112391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29515337683/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-112391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c59 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-851809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3237781/5000000) (δ := 2513/200000000) (ψ := -540941/500000) 250 162
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t59 : ((-110902671351/1000000000000 : ℚ) : ℝ) ≤ stT250 59 := by
  have hc : ((-851859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110902671351/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-851859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c60 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((873323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318009/2500000) (δ := 12531/1000000000) (ψ := -540941/500000) 250 163
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t60 : ((563695101681/5000000000000 : ℚ) : ℝ) ≤ stT250 60 := by
  have hc : ((873273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563695101681/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((873273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c61 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-71189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -821023/2000000) (δ := 789/62500000) (ψ := -540941/500000) 250 164
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t61 : ((-91212207191/10000000000000 : ℚ) : ℝ) ≤ stT250 61 := by
  have hc : ((-71239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91212207191/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-71239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c62 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-150557/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3028849/5000000) (δ := 12579/1000000000) (ψ := -540941/500000) 250 164
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t62 : ((-95610195567/1000000000000 : ℚ) : ℝ) ≤ stT250 62 := by
  have hc : ((-150567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95610195567/1000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-150567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c63 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((990217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69997/2000000) (δ := 6343/500000000) (ψ := -540941/500000) 250 165
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t63 : ((1247492590127/10000000000000 : ℚ) : ℝ) ≤ stT250 63 := by
  have hc : ((990167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1247492590127/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((990167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c64 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-118687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5515291/10000000) (δ := 12593/1000000000) (ψ := -540941/500000) 250 166
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t64 : ((-148371368697/2000000000000 : ℚ) : ℝ) ≤ stT250 64 := by
  have hc : ((-118697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148371368697/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-118697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c65 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-3959/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2087417/5000000) (δ := 12593/1000000000) (ψ := -540941/500000) 250 166
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t65 : ((-1228254607/100000000000 : ℚ) : ℝ) ≤ stT250 65 := by
  have hc : ((-3961/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1228254607/100000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-3961/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c66 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((699301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -995471/5000000) (δ := 12503/1000000000) (ψ := -540941/500000) 250 167
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t66 : ((430358922707/5000000000000 : ℚ) : ℝ) ≤ stT250 66 := by
  have hc : ((699251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430358922707/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((699251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c67 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-61507/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3703873/5000000) (δ := 127/10000000) (ψ := -540941/500000) 250 167
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t67 : ((-120234579459/1000000000000 : ℚ) : ℝ) ≤ stT250 67 := by
  have hc : ((-492081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120234579459/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-492081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c68 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((92729/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47961/500000) (δ := 197/15625000) (ψ := -540941/500000) 250 168
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t68 : ((14055544359/125000000000 : ℚ) : ℝ) ≤ stT250 68 := by
  have hc : ((23181/25000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14055544359/125000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((23181/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c69 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-39251/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2812247/5000000) (δ := 793/62500000) (ψ := -540941/500000) 250 169
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t69 : ((-378051453347/5000000000000 : ℚ) : ℝ) ≤ stT250 69 := by
  have hc : ((-314033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378051453347/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-314033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c70 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((44313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842111/2500000) (δ := 2503/200000000) (ψ := -540941/500000) 250 169
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t70 : ((13238046521/500000000000 : ℚ) : ℝ) ≤ stT250 70 := by
  have hc : ((44303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13238046521/500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((44303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c71 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((3603/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108567/312500) (δ := 6311/500000000) (ψ := -540941/500000) 250 170
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t71 : ((2137392581/100000000000 : ℚ) : ℝ) ≤ stT250 71 := by
  have hc : ((1801/10000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2137392581/100000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((1801/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c72 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-102161/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5267293/10000000) (δ := 12581/1000000000) (ψ := -540941/500000) 250 170
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t72 : ((-7525609347/125000000000 : ℚ) : ℝ) ≤ stT250 72 := by
  have hc : ((-102171/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7525609347/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-102171/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c73 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((46659/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -909929/5000000) (δ := 6337/500000000) (ψ := -540941/500000) 250 171
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t73 : ((436852394517/5000000000000 : ℚ) : ℝ) ≤ stT250 73 := by
  have hc : ((373247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436852394517/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((373247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c74 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-892411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3341821/5000000) (δ := 6337/500000000) (ψ := -540941/500000) 250 171
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t74 : ((-1037465385897/10000000000000 : ℚ) : ℝ) ≤ stT250 74 := by
  have hc : ((-892461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1037465385897/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-892461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c75 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((967927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -634883/10000000) (δ := 3159/250000000) (ψ := -540941/500000) 250 172
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t75 : ((11176075719/100000000000 : ℚ) : ℝ) ≤ stT250 75 := by
  have hc : ((967877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11176075719/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((967877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c76 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-996453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7643367/10000000) (δ := 3159/250000000) (ψ := -540941/500000) 250 172
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t76 : ((-1143067664737/10000000000000 : ℚ) : ℝ) ≤ stT250 76 := by
  have hc : ((-996503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1143067664737/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-996503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c77 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((99911/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52733/5000000) (δ := 49/3906250) (ψ := -540941/500000) 250 173
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t77 : ((11385337713/100000000000 : ℚ) : ℝ) ≤ stT250 77 := by
  have hc : ((49953/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11385337713/100000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((49953/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c78 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-992017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471117/625000) (δ := 12651/1000000000) (ψ := -540941/500000) 250 174
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t78 : ((-561647819313/5000000000000 : ℚ) : ℝ) ≤ stT250 78 := by
  have hc : ((-992067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-561647819313/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-992067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c79 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((246413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 424003/10000000) (δ := 12651/1000000000) (ψ := -540941/500000) 250 174
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t79 : ((554443998687/5000000000000 : ℚ) : ℝ) ≤ stT250 79 := by
  have hc : ((492801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((554443998687/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((492801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c80 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-985123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7422211/10000000) (δ := 2529/200000000) (ψ := -540941/500000) 250 175
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t80 : ((-550728454941/5000000000000 : ℚ) : ℝ) ≤ stT250 80 := by
  have hc : ((-985173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550728454941/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-985173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c81 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((495333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85463/2500000) (δ := 6279/500000000) (ψ := -540941/500000) 250 175
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t81 : ((137585541797/1250000000000 : ℚ) : ℝ) ≤ stT250 81 := by
  have hc : ((123827/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137585541797/1250000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((123827/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c82 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-998037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7697299/10000000) (δ := 6269/500000000) (ψ := -540941/500000) 250 176
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t82 : ((-275550860873/2500000000000 : ℚ) : ℝ) ≤ stT250 82 := by
  have hc : ((-998087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275550860873/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-998087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c83 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((998821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7589/625000) (δ := 6269/500000000) (ψ := -540941/500000) 250 176
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t83 : ((548146498991/5000000000000 : ℚ) : ℝ) ≤ stT250 83 := by
  have hc : ((998771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548146498991/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((998771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c84 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-980829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736367/1000000) (δ := 5013/200000000) (ψ := -540941/500000) 250 176
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t84 : ((-107022726811/1000000000000 : ℚ) : ℝ) ≤ stT250 84 := by
  have hc : ((-980879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107022726811/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-980879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c85 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((232249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -473881/5000000) (δ := 3143/250000000) (ψ := -540941/500000) 250 177
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t85 : ((125947892099/1250000000000 : ℚ) : ℝ) ≤ stT250 85 := by
  have hc : ((464473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125947892099/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((464473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c86 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-206799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3181119/5000000) (δ := 3143/250000000) (ψ := -540941/500000) 250 177
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t86 : ((-55752657793/625000000000 : ℚ) : ℝ) ≤ stT250 86 := by
  have hc : ((-413623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55752657793/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-413623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c87 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((132287/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2120163/10000000) (δ := 3131/250000000) (ψ := -540941/500000) 250 178
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t87 : ((8863484939/125000000000 : ℚ) : ℝ) ≤ stT250 87 := by
  have hc : ((132277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8863484939/125000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((132277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c88 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-424413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200911/400000) (δ := 12679/1000000000) (ψ := -540941/500000) 250 178
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t88 : ((-113119813963/2500000000000 : ℚ) : ℝ) ≤ stT250 88 := by
  have hc : ((-424463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113119813963/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-424463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c89 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((121297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3623001/10000000) (δ := 12587/1000000000) (ψ := -540941/500000) 250 179
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t89 : ((128521456259/10000000000000 : ℚ) : ℝ) ≤ stT250 89 := by
  have hc : ((121247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128521456259/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((121247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c90 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((7023/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3360311/10000000) (δ := 1577/125000000) (ψ := -540941/500000) 250 179
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t90 : ((29604964389/1250000000000 : ℚ) : ℝ) ≤ stT250 90 := by
  have hc : ((112343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29604964389/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((112343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c91 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-284711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -680187/1250000) (δ := 25109/1000000000) (ψ := -540941/500000) 250 180
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t91 : ((-932763993/15625000000 : ℚ) : ℝ) ≤ stT250 91 := by
  have hc : ((-8898/15625 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-932763993/15625000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-8898/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c92 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((16991/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389161/10000000) (δ := 6347/500000000) (ψ := -540941/500000) 250 180
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t92 : ((442832457/5000000000 : ℚ) : ℝ) ≤ stT250 92 := by
  have hc : ((1699/2000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442832457/5000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((1699/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c93 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-993187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -756199/1000000) (δ := 12601/1000000000) (ψ := -540941/500000) 250 181
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t93 : ((-128742386703/1250000000000 : ℚ) : ℝ) ≤ stT250 93 := by
  have hc : ((-993237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128742386703/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-993237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c94 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((939039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219357/2500000) (δ := 6301/500000000) (ψ := -540941/500000) 250 181
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t94 : ((968492973369/10000000000000 : ℚ) : ℝ) ≤ stT250 94 := by
  have hc : ((938989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968492973369/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((938989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c95 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-132441/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1147277/2000000) (δ := 12601/1000000000) (ψ := -540941/500000) 250 181
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t95 : ((-135891944529/2000000000000 : ℚ) : ℝ) ≤ stT250 95 := by
  have hc : ((-132451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135891944529/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-132451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c96 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((198659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -428377/1250000) (δ := 3127/250000000) (ψ := -540941/500000) 250 182
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t96 : ((10135215879/500000000000 : ℚ) : ℝ) ≤ stT250 96 := by
  have hc : ((198609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10135215879/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((198609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c97 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((171873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1524867/5000000) (δ := 3127/250000000) (ψ := -540941/500000) 250 182
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t97 : ((10905323713/312500000000 : ℚ) : ℝ) ≤ stT250 97 := by
  have hc : ((21481/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10905323713/312500000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((21481/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c98 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-160129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6247917/10000000) (δ := 3147/250000000) (ψ := -540941/500000) 250 183
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t98 : ((-161764891267/2000000000000 : ℚ) : ℝ) ≤ stT250 98 := by
  have hc : ((-160139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161764891267/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-160139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c99 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((499621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97333/10000000) (δ := 3147/250000000) (ψ := -540941/500000) 250 183
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t99 : ((125528116263/1250000000000 : ℚ) : ℝ) ≤ stT250 99 := by
  have hc : ((124899/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125528116263/1250000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((124899/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c100 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-415447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6378771/10000000) (δ := 2523/200000000) (ψ := -540941/500000) 250 183
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t100 : ((-25967/312500 : ℚ) : ℝ) ≤ stT250 100 := by
  have hc : ((-25967/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25967/312500 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-25967/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c101 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((320937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3110193/10000000) (δ := 317/25000000) (ψ := -540941/500000) 250 184
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t101 : ((319294437819/10000000000000 : ℚ) : ℝ) ≤ stT250 101 := by
  have hc : ((320887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319294437819/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((320887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c102 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((344587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609499/2000000) (δ := 12523/1000000000) (ψ := -540941/500000) 250 184
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t102 : ((341142276939/10000000000000 : ℚ) : ℝ) ≤ stT250 102 := by
  have hc : ((344537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341142276939/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((344537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c103 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-869587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3281453/5000000) (δ := 12573/1000000000) (ψ := -540941/500000) 250 185
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t103 : ((-85687942521/1000000000000 : ℚ) : ℝ) ≤ stT250 103 := by
  have hc : ((-869637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85687942521/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-869637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c104 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((61131/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262109/5000000) (δ := 1263/100000000) (ψ := -540941/500000) 250 185
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t104 : ((23976308667/250000000000 : ℚ) : ℝ) ≤ stT250 104 := by
  have hc : ((489023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23976308667/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((489023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c105 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-574417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5456719/10000000) (δ := 12573/1000000000) (ψ := -540941/500000) 250 185
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t105 : ((-560622919767/10000000000000 : ℚ) : ℝ) ≤ stT250 105 := by
  have hc : ((-574467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560622919767/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-574467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c106 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-9959/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4327057/10000000) (δ := 6333/500000000) (ψ := -540941/500000) 250 186
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t106 : ((-38704290171/2500000000000 : ℚ) : ℝ) ≤ stT250 106 := by
  have hc : ((-79697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38704290171/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-79697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c107 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((407917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24087/156250) (δ := 6333/500000000) (ψ := -540941/500000) 250 186
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t107 : ((6161310633/78125000000 : ℚ) : ℝ) ≤ stT250 107 := by
  have hc : ((101973/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6161310633/78125000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((101973/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c108 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-30631/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 459723/625000) (δ := 6333/500000000) (ψ := -540941/500000) 250 186
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t108 : ((-471619422371/5000000000000 : ℚ) : ℝ) ≤ stT250 108 := by
  have hc : ((-490121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471619422371/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-490121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c109 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((50897/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -129601/500000) (δ := 12559/1000000000) (ψ := -540941/500000) 250 187
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t109 : ((6093210099/125000000000 : ℚ) : ℝ) ≤ stT250 109 := by
  have hc : ((12723/25000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6093210099/125000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((12723/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c110 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((63763/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3115793/10000000) (δ := 3161/250000000) (ψ := -540941/500000) 250 187
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t110 : ((30393031443/1000000000000 : ℚ) : ℝ) ≤ stT250 110 := by
  have hc : ((63753/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30393031443/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((63753/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c111 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-116667/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6935983/10000000) (δ := 12551/1000000000) (ψ := -540941/500000) 250 188
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t111 : ((-221482697247/2500000000000 : ℚ) : ℝ) ≤ stT250 111 := by
  have hc : ((-466693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221482697247/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-466693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c112 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((861671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83163/625000) (δ := 12551/1000000000) (ψ := -540941/500000) 250 188
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t112 : ((814155160731/10000000000000 : ℚ) : ℝ) ≤ stT250 112 := by
  have hc : ((861621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((814155160731/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((861621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c113 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-7433/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4225017/10000000) (δ := 12551/1000000000) (ψ := -540941/500000) 250 188
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t113 : ((-55962551569/5000000000000 : ℚ) : ℝ) ≤ stT250 113 := by
  have hc : ((-59489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55962551569/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-59489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c114 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-730963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5976321/10000000) (δ := 6329/500000000) (ψ := -540941/500000) 250 189
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t114 : ((-342328270809/5000000000000 : ℚ) : ℝ) ≤ stT250 114 := by
  have hc : ((-731013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342328270809/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-731013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c115 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((978631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -517759/10000000) (δ := 2509/200000000) (ψ := -540941/500000) 250 189
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t115 : ((114066337103/1250000000000 : ℚ) : ℝ) ≤ stT250 115 := by
  have hc : ((978581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114066337103/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((978581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c116 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-188521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4893491/10000000) (δ := 2509/200000000) (ψ := -540941/500000) 250 189
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t116 : ((-87530312221/2500000000000 : ℚ) : ℝ) ≤ stT250 116 := by
  have hc : ((-94273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87530312221/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-94273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c117 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-286041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5449597/10000000) (δ := 6283/500000000) (ψ := -540941/500000) 250 190
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t117 : ((-132234151533/2500000000000 : ℚ) : ℝ) ≤ stT250 117 := by
  have hc : ((-143033/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132234151533/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-143033/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c118 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((12483/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13041/1000000) (δ := 12637/1000000000) (ψ := -540941/500000) 250 190
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t118 : ((45963799533/500000000000 : ℚ) : ℝ) ≤ stT250 118 := by
  have hc : ((99859/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45963799533/500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((99859/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c119 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-467747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32149/62500) (δ := 12637/1000000000) (ψ := -540941/500000) 250 190
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t119 : ((-428829042103/10000000000000 : ℚ) : ℝ) ≤ stT250 119 := by
  have hc : ((-467797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428829042103/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-467797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c120 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-266769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1066787/2000000) (δ := 12673/1000000000) (ψ := -540941/500000) 250 191
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t120 : ((-121774252787/2500000000000 : ℚ) : ℝ) ≤ stT250 120 := by
  have hc : ((-133397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121774252787/2500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-133397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c121 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((998267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29437/2000000) (δ := 12673/1000000000) (ψ := -540941/500000) 250 191
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t121 : ((90746909253/1000000000000 : ℚ) : ℝ) ≤ stT250 121 := by
  have hc : ((998217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90746909253/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((998217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c122 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-415011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4996877/10000000) (δ := 1253/100000000) (ψ := -540941/500000) 250 191
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t122 : ((-187889398419/5000000000000 : ℚ) : ℝ) ≤ stT250 122 := by
  have hc : ((-415061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187889398419/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-415061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c123 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-623189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87641/156250) (δ := 12623/1000000000) (ψ := -540941/500000) 250 192
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t123 : ((-56195590913/1000000000000 : ℚ) : ℝ) ≤ stT250 123 := by
  have hc : ((-623239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56195590913/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-623239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c124 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((61003/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274137/5000000) (δ := 12623/1000000000) (ψ := -540941/500000) 250 192
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t124 : ((219117894987/2500000000000 : ℚ) : ℝ) ≤ stT250 124 := by
  have hc : ((487999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219117894987/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((487999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c125 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-216223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4471851/10000000) (δ := 12623/1000000000) (ψ := -540941/500000) 250 192
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t125 : ((-48360156711/2500000000000 : ℚ) : ℝ) ≤ stT250 125 := by
  have hc : ((-216273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48360156711/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-216273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c126 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-32103/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6255987/10000000) (δ := 3129/250000000) (ψ := -540941/500000) 250 193
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t126 : ((-5720282691/80000000000 : ℚ) : ℝ) ≤ stT250 126 := by
  have hc : ((-6421/8000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5720282691/80000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-6421/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c127 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((432381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1315299/10000000) (δ := 12687/1000000000) (ψ := -540941/500000) 250 193
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t127 : ((23978355671/312500000000 : ℚ) : ℝ) ≤ stT250 127 := by
  have hc : ((108089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23978355671/312500000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((108089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c128 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((8481/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3586701/10000000) (δ := 12687/1000000000) (ψ := -540941/500000) 250 193
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t128 : ((59947596709/5000000000000 : ℚ) : ℝ) ≤ stT250 128 := by
  have hc : ((67823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59947596709/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((67823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c129 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-971661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1814347/2500000) (δ := 12609/1000000000) (ψ := -540941/500000) 250 194
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t129 : ((-855543921661/10000000000000 : ℚ) : ℝ) ≤ stT250 129 := by
  have hc : ((-971711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-855543921661/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-971711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c130 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((563273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1215569/5000000) (δ := 12609/1000000000) (ψ := -540941/500000) 250 194
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t130 : ((246989618967/5000000000000 : ℚ) : ℝ) ≤ stT250 130 := by
  have hc : ((563223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246989618967/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((563223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c131 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((73393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94327/400000) (δ := 6297/500000000) (ψ := -540941/500000) 250 194
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t131 : ((32059148511/625000000000 : ℚ) : ℝ) ≤ stT250 131 := by
  have hc : ((293547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32059148511/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((293547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c132 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-119521/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142221/200000) (δ := 6297/500000000) (ψ := -540941/500000) 250 194
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t132 : ((-416140814401/5000000000000 : ℚ) : ℝ) ≤ stT250 132 := by
  have hc : ((-478109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416140814401/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-478109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c133 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((1883/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1939957/5000000) (δ := 12701/1000000000) (ψ := -540941/500000) 250 195
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t133 : ((814215351/500000000000 : ℚ) : ℝ) ≤ stT250 133 := by
  have hc : ((939/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((814215351/500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((939/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c134 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((118627/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 801743/10000000) (δ := 12551/500000000) (ψ := -540941/500000) 250 195
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t134 : ((102472670061/1250000000000 : ℚ) : ℝ) ≤ stT250 134 := by
  have hc : ((474483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102472670061/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((474483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c135 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-571751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2724293/5000000) (δ := 12701/1000000000) (ψ := -540941/500000) 250 195
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t135 : ((-492127964063/10000000000000 : ℚ) : ℝ) ≤ stT250 135 := by
  have hc : ((-571801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492127964063/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-571801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c136 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-634939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2823407/5000000) (δ := 12609/1000000000) (ψ := -540941/500000) 250 196
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t136 : ((-544498622577/10000000000000 : ℚ) : ℝ) ≤ stT250 136 := by
  have hc : ((-634989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544498622577/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-634989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c137 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((910129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -534001/5000000) (δ := 6297/500000000) (ψ := -540941/500000) 250 196
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t137 : ((777532364203/10000000000000 : ℚ) : ℝ) ≤ stT250 137 := by
  have hc : ((910079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((777532364203/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((910079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c138 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((89427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 869359/2500000) (δ := 12609/1000000000) (ψ := -540941/500000) 250 196
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t138 : ((4756499307/312500000000 : ℚ) : ℝ) ≤ stT250 138 := by
  have hc : ((44701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4756499307/312500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((44701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c139 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-499259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96473/125000) (δ := 3129/250000000) (ψ := -540941/500000) 250 197
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t139 : ((-105871799169/1250000000000 : ℚ) : ℝ) ≤ stT250 139 := by
  have hc : ((-124821/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105871799169/1250000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-124821/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c140 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((136151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404691/1250000) (δ := 12687/1000000000) (ψ := -540941/500000) 250 197
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t140 : ((28761858351/1250000000000 : ℚ) : ℝ) ≤ stT250 140 := by
  have hc : ((68063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28761858351/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((68063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c141 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((884983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1210847/10000000) (δ := 12687/1000000000) (ψ := -540941/500000) 250 197
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t141 : ((745247210883/10000000000000 : ℚ) : ℝ) ≤ stT250 141 := by
  have hc : ((884933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((745247210883/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((884933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c142 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-629059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5627847/10000000) (δ := 12687/1000000000) (ψ := -540941/500000) 250 197
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t142 : ((-263968474419/5000000000000 : ℚ) : ℝ) ≤ stT250 142 := by
  have hc : ((-629109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263968474419/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-629109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c143 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-324721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1423529/2500000) (δ := 629/50000000) (ψ := -540941/500000) 250 198
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t143 : ((-135783284639/2500000000000 : ℚ) : ℝ) ≤ stT250 143 := by
  have hc : ((-162373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135783284639/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-162373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c144 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((172003/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1338741/10000000) (δ := 629/50000000) (ψ := -540941/500000) 250 198
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t144 : ((143327442669/2000000000000 : ℚ) : ℝ) ≤ stT250 144 := by
  have hc : ((171993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143327442669/2000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((171993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c145 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((367359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 746643/2500000) (δ := 12623/1000000000) (ψ := -540941/500000) 250 198
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t145 : ((152516614143/5000000000000 : ℚ) : ℝ) ≤ stT250 145 := by
  have hc : ((367309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152516614143/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((367309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c146 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-973953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3641067/5000000) (δ := 629/50000000) (ψ := -540941/500000) 250 198
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t146 : ((-403045363409/5000000000000 : ℚ) : ℝ) ≤ stT250 146 := by
  have hc : ((-974003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403045363409/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-974003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c147 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-46463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2079821/5000000) (δ := 12673/1000000000) (ψ := -540941/500000) 250 199
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t147 : ((-4792837257/625000000000 : ℚ) : ℝ) ≤ stT250 147 := by
  have hc : ((-5811/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4792837257/625000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-5811/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c148 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((999517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77671/10000000) (δ := 1253/100000000) (ψ := -540941/500000) 250 199
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t148 : ((410777938599/5000000000000 : ℚ) : ℝ) ≤ stT250 148 := by
  have hc : ((999467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410777938599/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((999467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c149 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-71651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4286483/10000000) (δ := 12673/1000000000) (ψ := -540941/500000) 250 199
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t149 : ((-458744319/39062500000 : ℚ) : ℝ) ≤ stT250 149 := by
  have hc : ((-17919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458744319/39062500000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-17919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c150 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-970083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7240917/10000000) (δ := 12637/1000000000) (ψ := -540941/500000) 250 200
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t150 : ((-792110684101/10000000000000 : ℚ) : ℝ) ≤ stT250 150 := by
  have hc : ((-970133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-792110684101/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-970133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c151 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((82329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544021/5000000) (δ := 12637/1000000000) (ψ := -540941/500000) 250 200
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t151 : ((33494089951/1250000000000 : ℚ) : ℝ) ≤ stT250 151 := by
  have hc : ((164633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33494089951/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((164633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c152 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((915133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207479/2000000) (δ := 6283/500000000) (ψ := -540941/500000) 250 200
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t152 : ((742230226881/10000000000000 : ℚ) : ℝ) ≤ stT250 152 := by
  have hc : ((915083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((742230226881/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((915083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c153 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-464891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513577/1000000) (δ := 6283/500000000) (ψ := -540941/500000) 250 200
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t153 : ((-375882946273/10000000000000 : ℚ) : ℝ) ≤ stT250 153 := by
  have hc : ((-464941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375882946273/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-464941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c154 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-856993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3250253/5000000) (δ := 6329/500000000) (ψ := -540941/500000) 250 201
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t154 : ((-690624961389/10000000000000 : ℚ) : ℝ) ≤ stT250 154 := by
  have hc : ((-857043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-690624961389/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-857043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c155 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((17353/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2455193/10000000) (δ := 2509/200000000) (ψ := -540941/500000) 250 201
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t155 : ((222992068437/5000000000000 : ℚ) : ℝ) ≤ stT250 155 := by
  have hc : ((277623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222992068437/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((277623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c156 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((101323/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1564119/10000000) (δ := 6329/500000000) (ψ := -540941/500000) 250 201
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t156 : ((506989017/7812500000 : ℚ) : ℝ) ≤ stT250 156 := by
  have hc : ((405267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506989017/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((405267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c157 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-607017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 347359/625000) (δ := 6329/500000000) (ψ := -540941/500000) 250 201
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t157 : ((-484492280829/10000000000000 : ℚ) : ℝ) ≤ stT250 157 := by
  have hc : ((-607067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484492280829/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-607067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c158 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-784563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6181969/10000000) (δ := 12551/1000000000) (ψ := -540941/500000) 250 202
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t158 : ((-312102574527/5000000000000 : ℚ) : ℝ) ≤ stT250 158 := by
  have hc : ((-784613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312102574527/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-784613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c159 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((312569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2238719/10000000) (δ := 12551/1000000000) (ψ := -540941/500000) 250 202
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t159 : ((7745729117/156250000000 : ℚ) : ℝ) ≤ stT250 159 := by
  have hc : ((9767/15625 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7745729117/156250000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((9767/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c160 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((782633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1679781/10000000) (δ := 12551/1000000000) (ψ := -540941/500000) 250 202
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t160 : ((618685859727/10000000000000 : ℚ) : ℝ) ≤ stT250 160 := by
  have hc : ((782583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618685859727/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((782583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c161 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-306061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1393461/2500000) (δ := 3163/250000000) (ψ := -540941/500000) 250 202
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t161 : ((-120614871773/2500000000000 : ℚ) : ℝ) ≤ stT250 161 := by
  have hc : ((-153043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120614871773/2500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-153043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c162 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-804511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156603/250000) (δ := 3161/250000000) (ψ := -540941/500000) 250 203
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t162 : ((-25284938547/400000000000 : ℚ) : ℝ) ≤ stT250 162 := by
  have hc : ((-804561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25284938547/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-804561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c163 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((567629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604483/2500000) (δ := 12559/1000000000) (ψ := -540941/500000) 250 203
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t163 : ((22228096377/500000000000 : ℚ) : ℝ) ≤ stT250 163 := by
  have hc : ((567579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22228096377/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((567579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c164 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((52891/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1404693/10000000) (δ := 12559/1000000000) (ψ := -540941/500000) 250 203
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t164 : ((82596898351/1250000000000 : ℚ) : ℝ) ≤ stT250 164 := by
  have hc : ((423103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82596898351/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((423103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c165 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-244451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1301017/2500000) (δ := 12559/1000000000) (ψ := -540941/500000) 250 203
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t165 : ((-47581080381/1250000000000 : ℚ) : ℝ) ≤ stT250 165 := by
  have hc : ((-61119/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47581080381/1250000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-61119/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c166 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-450091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3363729/5000000) (δ := 12537/1000000000) (ψ := -540941/500000) 250 204
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t166 : ((-87339495879/1250000000000 : ℚ) : ℝ) ≤ stT250 166 := by
  have hc : ((-112529/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87339495879/1250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-112529/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c167 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((372163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594729/2000000) (δ := 6333/500000000) (ψ := -540941/500000) 250 204
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t167 : ((287949597999/10000000000000 : ℚ) : ℝ) ≤ stT250 167 := by
  have hc : ((372113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287949597999/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((372113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c168 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((477213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757667/10000000) (δ := 12537/1000000000) (ψ := -540941/500000) 250 204
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t168 : ((23009886063/312500000000 : ℚ) : ℝ) ≤ stT250 168 := by
  have hc : ((119297/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23009886063/312500000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((119297/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c169 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-42859/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4466917/10000000) (δ := 12537/1000000000) (ψ := -540941/500000) 250 204
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t169 : ((-32976163739/2000000000000 : ℚ) : ℝ) ≤ stT250 169 := by
  have hc : ((-42869/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32976163739/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-42869/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c170 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-992797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3776867/5000000) (δ := 1263/100000000) (ψ := -540941/500000) 250 205
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t170 : ((-152295779871/2000000000000 : ℚ) : ℝ) ≤ stT250 170 := by
  have hc : ((-992847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152295779871/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-992847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c171 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((15577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1944023/5000000) (δ := 12573/1000000000) (ψ := -540941/500000) 250 205
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t171 : ((11873791913/10000000000000 : ℚ) : ℝ) ≤ stT250 171 := by
  have hc : ((15527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11873791913/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((15527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c172 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((995251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121867/5000000) (δ := 1263/100000000) (ψ := -540941/500000) 250 205
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t172 : ((189708200223/2500000000000 : ℚ) : ℝ) ≤ stT250 172 := by
  have hc : ((995201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189708200223/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((995201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c173 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((54317/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1689727/5000000) (δ := 12573/1000000000) (ψ := -540941/500000) 250 205
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t173 : ((16514758713/1000000000000 : ℚ) : ℝ) ≤ stT250 173 := by
  have hc : ((108609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16514758713/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((108609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c174 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-469877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3490883/5000000) (δ := 1263/100000000) (ψ := -540941/500000) 250 205
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t174 : ((-178116118149/2500000000000 : ℚ) : ℝ) ≤ stT250 174 := by
  have hc : ((-234951/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178116118149/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-234951/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c175 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-467983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5144509/10000000) (δ := 317/25000000) (ψ := -540941/500000) 250 206
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t175 : ((-353799717657/10000000000000 : ℚ) : ℝ) ≤ stT250 175 := by
  have hc : ((-468033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353799717657/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-468033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c176 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((806077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1583259/10000000) (δ := 317/25000000) (ψ := -540941/500000) 250 206
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t176 : ((303782710003/5000000000000 : ℚ) : ℝ) ≤ stT250 176 := by
  have hc : ((806027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303782710003/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((806027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c177 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((708697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978933/5000000) (δ := 317/25000000) (ψ := -540941/500000) 250 206
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t177 : ((266325841481/5000000000000 : ℚ) : ℝ) ≤ stT250 177 := by
  have hc : ((708647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266325841481/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((708647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c178 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-290843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5478991/10000000) (δ := 317/25000000) (ψ := -540941/500000) 250 206
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t178 : ((-13625929611/312500000000 : ℚ) : ℝ) ≤ stT250 178 := by
  have hc : ((-72717/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13625929611/312500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-72717/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c179 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-180039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1345507/2000000) (δ := 3147/250000000) (ψ := -540941/500000) 250 207
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t179 : ((-33643776091/500000000000 : ℚ) : ℝ) ≤ stT250 179 := by
  have hc : ((-180049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33643776091/500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-180049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c180 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((269171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162283/500000) (δ := 3147/250000000) (ψ := -540941/500000) 250 207
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t180 : ((40118136591/2000000000000 : ℚ) : ℝ) ≤ stT250 180 := by
  have hc : ((269121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40118136591/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((269121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c181 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((249059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43393/2000000) (δ := 3147/250000000) (ψ := -540941/500000) 250 207
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t181 : ((185114769171/2500000000000 : ℚ) : ℝ) ≤ stT250 181 := by
  have hc : ((498093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185114769171/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((498093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c182 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((13301/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 732093/2000000) (δ := 3147/250000000) (ψ := -540941/500000) 250 207
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t182 : ((39418880571/5000000000000 : ℚ) : ℝ) ≤ stT250 182 := by
  have hc : ((53179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39418880571/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((53179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c183 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-238271/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221411/312500) (δ := 2523/200000000) (ψ := -540941/500000) 250 207
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t183 : ((-176144405437/2500000000000 : ℚ) : ℝ) ≤ stT250 183 := by
  have hc : ((-476567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176144405437/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-476567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c184 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-246671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5216811/10000000) (δ := 3127/250000000) (ψ := -540941/500000) 250 208
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t184 : ((-2273334477/62500000000 : ℚ) : ℝ) ≤ stT250 184 := by
  have hc : ((-30837/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2273334477/62500000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-30837/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c185 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((18601/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14291/78125) (δ := 2539/200000000) (ψ := -540941/500000) 250 208
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t185 : ((27349593193/500000000000 : ℚ) : ℝ) ≤ stT250 185 := by
  have hc : ((74399/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27349593193/500000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((74399/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c186 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((204049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 770001/5000000) (δ := 2539/200000000) (ψ := -540941/500000) 250 208
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t186 : ((59842681231/1000000000000 : ℚ) : ℝ) ≤ stT250 186 := by
  have hc : ((408073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59842681231/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((408073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c187 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-94053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1222813/2500000) (δ := 2539/200000000) (ψ := -540941/500000) 250 208
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t187 : ((-137575120763/5000000000000 : ℚ) : ℝ) ≤ stT250 187 := by
  have hc : ((-188131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137575120763/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-188131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c188 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-494517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7483399/10000000) (δ := 6301/500000000) (ψ := -540941/500000) 250 209
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t188 : ((-7213636883/100000000000 : ℚ) : ℝ) ≤ stT250 188 := by
  have hc : ((-247271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7213636883/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-247271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c189 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-4807/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130241/312500) (δ := 12601/1000000000) (ψ := -540941/500000) 250 209
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t189 : ((-6996793267/1000000000000 : ℚ) : ℝ) ≤ stT250 189 := by
  have hc : ((-9619/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6996793267/1000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-9619/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c190 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((940113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869587/10000000) (δ := 12601/1000000000) (ψ := -540941/500000) 250 209
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t190 : ((170498286247/2500000000000 : ℚ) : ℝ) ≤ stT250 190 := by
  have hc : ((940063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170498286247/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((940063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c191 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((113963/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 301411/1250000) (δ := 12601/1000000000) (ψ := -540941/500000) 250 209
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t191 : ((41226714011/1000000000000 : ℚ) : ℝ) ≤ stT250 191 := by
  have hc : ((113953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41226714011/1000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((113953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c192 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-643601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177343/312500) (δ := 6301/500000000) (ψ := -540941/500000) 250 209
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t192 : ((-58064400361/1250000000000 : ℚ) : ℝ) ≤ stT250 192 := by
  have hc : ((-643651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58064400361/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-643651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c193 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-227543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3393119/5000000) (δ := 6347/500000000) (ψ := -540941/500000) 250 210
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t193 : ((-40949522447/625000000000 : ℚ) : ℝ) ≤ stT250 193 := by
  have hc : ((-455111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40949522447/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-455111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c194 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((73879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1778119/5000000) (δ := 6347/500000000) (ψ := -540941/500000) 250 210
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t194 : ((13256017533/1250000000000 : ℚ) : ℝ) ≤ stT250 194 := by
  have hc : ((36927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13256017533/1250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((36927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c195 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((99061/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -342863/10000000) (δ := 6347/500000000) (ψ := -540941/500000) 250 210
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t195 : ((2216730887/31250000000 : ℚ) : ℝ) ≤ stT250 195 := by
  have hc : ((6191/6250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2216730887/31250000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((6191/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c196 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((416113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114163/400000) (δ := 12509/1000000000) (ψ := -540941/500000) 250 210
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t196 : ((59437511991/2000000000000 : ℚ) : ℝ) ≤ stT250 196 := by
  have hc : ((416063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59437511991/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((416063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c197 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-373357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3017381/5000000) (δ := 6347/500000000) (ψ := -540941/500000) 250 210
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t197 : ((-133011923461/2500000000000 : ℚ) : ℝ) ≤ stT250 197 := by
  have hc : ((-186691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133011923461/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-186691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c198 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-171733/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3254319/5000000) (δ := 1577/125000000) (ψ := -540941/500000) 250 211
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t198 : ((-12205259781/200000000000 : ℚ) : ℝ) ≤ stT250 198 := by
  have hc : ((-171743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12205259781/200000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-171743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c199 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((56213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3360013/10000000) (δ := 1577/125000000) (ψ := -540941/500000) 250 211
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t199 : ((79678933281/5000000000000 : ℚ) : ℝ) ≤ stT250 199 := by
  have hc : ((112401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79678933281/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((112401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c200 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((995873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227201/10000000) (δ := 12587/1000000000) (ψ := -540941/500000) 250 211
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t200 : ((352076209119/5000000000000 : ℚ) : ℝ) ≤ stT250 200 := by
  have hc : ((995823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352076209119/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((995823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c201 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((201493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2890049/10000000) (δ := 12587/1000000000) (ψ := -540941/500000) 250 211
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t201 : ((7105222323/250000000000 : ℚ) : ℝ) ≤ stT250 201 := by
  have hc : ((50367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7105222323/250000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((50367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c202 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-735157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5991737/10000000) (δ := 1577/125000000) (ψ := -540941/500000) 250 211
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t202 : ((-258645087393/5000000000000 : ℚ) : ℝ) ≤ stT250 202 := by
  have hc : ((-735207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258645087393/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-735207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c203 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-176497/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6629789/10000000) (δ := 3131/250000000) (ψ := -540941/500000) 250 212
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t203 : ((-123883732541/2000000000000 : ℚ) : ℝ) ≤ stT250 203 := by
  have hc : ((-176507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123883732541/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-176507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c204 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((4589/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3558539/10000000) (δ := 3131/250000000) (ψ := -540941/500000) 250 212
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t204 : ((2569478793/250000000000 : ℚ) : ℝ) ≤ stT250 204 := by
  have hc : ((73399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2569478793/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((73399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c205 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((244971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -502289/10000000) (δ := 3131/250000000) (ψ := -540941/500000) 250 212
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t205 : ((34217273031/500000000000 : ℚ) : ℝ) ≤ stT250 205 := by
  have hc : ((489917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34217273031/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((489917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c206 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((527081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1269543/5000000) (δ := 3131/250000000) (ψ := -540941/500000) 250 212
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t206 : ((367199889723/10000000000000 : ℚ) : ℝ) ≤ stT250 206 := by
  have hc : ((527031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367199889723/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((527031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c207 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-304773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5565711/10000000) (δ := 3131/250000000) (ψ := -540941/500000) 250 212
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t207 : ((-105924772551/2500000000000 : ℚ) : ℝ) ≤ stT250 207 := by
  have hc : ((-152399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105924772551/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-152399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c208 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-479191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -713019/1000000) (δ := 3143/250000000) (ψ := -540941/500000) 250 213
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t208 : ((-162244567/2441406250 : ℚ) : ℝ) ≤ stT250 208 := by
  have hc : ((-29951/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162244567/2441406250 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-29951/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c209 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-82137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826513/2000000) (δ := 3143/250000000) (ψ := -540941/500000) 250 213
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t209 : ((-11369996141/2000000000000 : ℚ) : ℝ) ≤ stT250 209 := by
  have hc : ((-82187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11369996141/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-82187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c210 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((179237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287313/2500000) (δ := 12631/1000000000) (ψ := -540941/500000) 250 213
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t210 : ((24735655951/400000000000 : ℚ) : ℝ) ≤ stT250 210 := by
  have hc : ((179227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24735655951/400000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((179227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c211 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((37327/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1819873/10000000) (δ := 12631/1000000000) (ψ := -540941/500000) 250 213
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t211 : ((12847615443/250000000000 : ℚ) : ℝ) ≤ stT250 211 := by
  have hc : ((74649/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12847615443/250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((74649/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c212 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-41589/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 954987/2000000) (δ := 3143/250000000) (ψ := -540941/500000) 250 213
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t212 : ((-114270969943/5000000000000 : ℚ) : ℝ) ≤ stT250 212 := by
  have hc : ((-166381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114270969943/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-166381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c213 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-12481/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7716123/10000000) (δ := 12631/1000000000) (ψ := -540941/500000) 250 213
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t213 : ((-68418177217/1000000000000 : ℚ) : ℝ) ≤ stT250 213 := by
  have hc : ((-99853/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68418177217/1000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-99853/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c214 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-439431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5064403/10000000) (δ := 6269/500000000) (ψ := -540941/500000) 250 214
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t214 : ((-150211529433/5000000000000 : ℚ) : ℝ) ≤ stT250 214 := by
  have hc : ((-439481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150211529433/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-439481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c215 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((652239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2150653/10000000) (δ := 6269/500000000) (ψ := -540941/500000) 250 214
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t215 : ((222394492433/5000000000000 : ℚ) : ℝ) ≤ stT250 215 := by
  have hc : ((652189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222394492433/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((652189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c216 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((119423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 749597/10000000) (δ := 6269/500000000) (ψ := -540941/500000) 250 214
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t216 : ((325010836471/5000000000000 : ℚ) : ℝ) ≤ stT250 216 := by
  have hc : ((477667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325010836471/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((477667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c217 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((115971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3636409/10000000) (δ := 2533/200000000) (ψ := -540941/500000) 250 214
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t217 : ((19673068831/2500000000000 : ℚ) : ℝ) ≤ stT250 217 := by
  have hc : ((115921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19673068831/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((115921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c218 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-429469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1627493/2500000) (δ := 6269/500000000) (ψ := -540941/500000) 250 214
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t218 : ((-72722568321/1250000000000 : ℚ) : ℝ) ≤ stT250 218 := by
  have hc : ((-214747/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72722568321/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-214747/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c219 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-102701/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3168777/5000000) (δ := 6279/500000000) (ψ := -540941/500000) 250 215
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t219 : ((-138806383401/2500000000000 : ℚ) : ℝ) ≤ stT250 219 := by
  have hc : ((-410829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138806383401/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-410829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c220 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((173837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3490179/10000000) (δ := 6279/500000000) (ψ := -540941/500000) 250 215
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t220 : ((117167021613/10000000000000 : ℚ) : ℝ) ≤ stT250 220 := by
  have hc : ((173787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117167021613/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((173787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c221 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((241451/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655679/10000000) (δ := 6279/500000000) (ψ := -540941/500000) 250 215
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t221 : ((10150557417/156250000000 : ℚ) : ℝ) ≤ stT250 221 := by
  have hc : ((482877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10150557417/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((482877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c222 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((64759/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1082973/5000000) (δ := 6279/500000000) (ψ := -540941/500000) 250 215
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t222 : ((5432504453/125000000000 : ℚ) : ℝ) ≤ stT250 222 := by
  have hc : ((32377/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5432504453/125000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((32377/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c223 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-407013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2487473/5000000) (δ := 6279/500000000) (ψ := -540941/500000) 250 215
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t223 : ((-5451794759/200000000000 : ℚ) : ℝ) ≤ stT250 223 := by
  have hc : ((-407063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5451794759/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-407063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c224 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-499727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 971423/1250000) (δ := 2529/200000000) (ψ := -540941/500000) 250 215
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t224 : ((-20869456113/312500000000 : ℚ) : ℝ) ≤ stT250 224 := by
  have hc : ((-62469/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20869456113/312500000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-62469/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c225 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-235417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -257629/500000) (δ := 12651/1000000000) (ψ := -540941/500000) 250 216
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t225 : ((-78480705907/2500000000000 : ℚ) : ℝ) ≤ stT250 225 := by
  have hc : ((-117721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78480705907/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-117721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c226 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((289867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190493/5000000) (δ := 25051/1000000000) (ψ := -540941/500000) 250 216
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t226 : ((9639999999/250000000000 : ℚ) : ℝ) ≤ stT250 226 := by
  have hc : ((144921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9639999999/250000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((144921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c227 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((494283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18921/500000) (δ := 12651/1000000000) (ψ := -540941/500000) 250 216
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t227 : ((164025201267/2500000000000 : ℚ) : ℝ) ≤ stT250 227 := by
  have hc : ((247129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164025201267/2500000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((247129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c228 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((78767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312567/1000000) (δ := 12651/1000000000) (ψ := -540941/500000) 250 216
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t228 : ((52156427697/2500000000000 : ℚ) : ℝ) ≤ stT250 228 := by
  have hc : ((157509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52156427697/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((157509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c229 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-139739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146523/250000) (δ := 12651/1000000000) (ψ := -540941/500000) 250 216
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t229 : ((-92348794431/2000000000000 : ℚ) : ℝ) ≤ stT250 229 := by
  have hc : ((-139749/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92348794431/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-139749/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c230 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-957641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -712373/1000000) (δ := 12659/1000000000) (ψ := -540941/500000) 250 217
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t230 : ((-631483249271/10000000000000 : ℚ) : ℝ) ≤ stT250 230 := by
  have hc : ((-957691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-631483249271/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-957691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c231 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-192879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -441223/1000000) (δ := 12659/1000000000) (ψ := -540941/500000) 250 217
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t231 : ((-3966813169/312500000000 : ℚ) : ℝ) ≤ stT250 231 := by
  have hc : ((-192929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3966813169/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-192929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c232 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((96803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10703/62500) (δ := 12659/1000000000) (ψ := -540941/500000) 250 217
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t232 : ((63550163871/1250000000000 : ℚ) : ℝ) ≤ stT250 232 := by
  have hc : ((387187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63550163871/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((387187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c233 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((462401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 975707/10000000) (δ := 49/3906250) (ψ := -540941/500000) 250 217
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t233 : ((37864028437/625000000000 : ℚ) : ℝ) ≤ stT250 233 := by
  have hc : ((57797/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37864028437/625000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((57797/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c234 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((54809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 730479/2000000) (δ := 12659/1000000000) (ψ := -540941/500000) 250 217
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t234 : ((1748701/244140625 : ℚ) : ℝ) ≤ stT250 234 := by
  have hc : ((1712/15625 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1748701/244140625 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((1712/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c235 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-408521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263529/2000000) (δ := 12659/1000000000) (ψ := -540941/500000) 250 217
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t235 : ((-133253201817/2500000000000 : ℚ) : ℝ) ≤ stT250 235 := by
  have hc : ((-204273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133253201817/2500000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-204273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c236 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-901731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6736381/10000000) (δ := 12567/1000000000) (ψ := -540941/500000) 250 218
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t236 : ((-117401966609/2000000000000 : ℚ) : ℝ) ≤ stT250 236 := by
  have hc : ((-901781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117401966609/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-901781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c237 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-8329/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2046847/5000000) (δ := 3159/250000000) (ψ := -540941/500000) 250 218
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t237 : ((-2165731337/500000000000 : ℚ) : ℝ) ≤ stT250 237 := by
  have hc : ((-33341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2165731337/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-33341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c238 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((416897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1462131/10000000) (δ := 12567/1000000000) (ψ := -540941/500000) 250 218
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t238 : ((33777210127/625000000000 : ℚ) : ℝ) ≤ stT250 238 := by
  have hc : ((52109/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33777210127/625000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((52109/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c239 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((17891/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1158431/10000000) (δ := 3159/250000000) (ψ := -540941/500000) 250 218
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t239 : ((578603747/10000000000 : ℚ) : ℝ) ≤ stT250 239 := by
  have hc : ((1789/2000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((578603747/10000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((1789/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c240 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((63531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 471007/1250000) (δ := 3159/250000000) (ψ := -540941/500000) 250 218
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t240 : ((40976795057/10000000000000 : ℚ) : ℝ) ≤ stT250 240 := by
  have hc : ((63481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40976795057/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((63481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c241 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-828221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3183403/5000000) (δ := 3159/250000000) (ψ := -540941/500000) 250 218
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t241 : ((-533536562547/10000000000000 : ℚ) : ℝ) ≤ stT250 241 := by
  have hc : ((-828271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-533536562547/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-828271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c242 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-904611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6753157/10000000) (δ := 12529/1000000000) (ψ := -540941/500000) 250 219
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t242 : ((-23261548293/400000000000 : ℚ) : ℝ) ≤ stT250 242 := by
  have hc : ((-904661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23261548293/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-904661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c243 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-99377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1043961/2500000) (δ := 6337/500000000) (ψ := -540941/500000) 250 219
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t243 : ((-63782519927/10000000000000 : ℚ) : ℝ) ≤ stT250 243 := by
  have hc : ((-99427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63782519927/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-99427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c244 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((399959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -804547/5000000) (δ := 6337/500000000) (ψ := -540941/500000) 250 219
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t244 : ((16001959241/312500000000 : ℚ) : ℝ) ≤ stT250 244 := by
  have hc : ((199967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16001959241/312500000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((199967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c245 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((929091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236781/2500000) (δ := 25129/1000000000) (ψ := -540941/500000) 250 219
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t245 : ((148385499479/2500000000000 : ℚ) : ℝ) ≤ stT250 245 := by
  have hc : ((929041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148385499479/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((929041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c246 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((86369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 436621/1250000) (δ := 12529/1000000000) (ψ := -540941/500000) 250 219
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t246 : ((860169721/78125000000 : ℚ) : ℝ) ≤ stT250 246 := by
  have hc : ((10793/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860169721/78125000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((10793/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c247 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-745037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1507117/2500000) (δ := 12529/1000000000) (ψ := -540941/500000) 250 219
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t247 : ((-94817536359/2000000000000 : ℚ) : ℝ) ≤ stT250 247 := by
  have hc : ((-745087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94817536359/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-745087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c248 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-192217/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1430849/2000000) (δ := 12581/1000000000) (ψ := -540941/500000) 250 220
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t248 : ((-122064337227/2000000000000 : ℚ) : ℝ) ≤ stT250 248 := by
  have hc : ((-192227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122064337227/2000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-192227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c249 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-281039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4639183/10000000) (δ := 6311/500000000) (ψ := -540941/500000) 250 220
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t249 : ((-7125325061/400000000000 : ℚ) : ℝ) ≤ stT250 249 := by
  have hc : ((-281089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7125325061/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-281089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c250 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((328619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53353/250000) (δ := 12581/1000000000) (ψ := -540941/500000) 250 220
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t250 : ((20782091827/500000000000 : ℚ) : ℝ) ≤ stT250 250 := by
  have hc : ((164297/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20782091827/500000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((164297/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c251 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((989599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4511/125000) (δ := 12581/1000000000) (ψ := -540941/500000) 250 220
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t251 : ((312298695753/5000000000000 : ℚ) : ℝ) ≤ stT250 251 := by
  have hc : ((989549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312298695753/5000000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((989549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c252 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((419069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1422971/5000000) (δ := 6311/500000000) (ψ := -540941/500000) 250 220
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t252 : ((13197841443/500000000000 : ℚ) : ℝ) ≤ stT250 252 := by
  have hc : ((419019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13197841443/500000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((419019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c253 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-26461/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665149/1250000) (δ := 6311/500000000) (ψ := -540941/500000) 250 220
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t253 : ((-6654988053/200000000000 : ℚ) : ℝ) ≤ stT250 253 := by
  have hc : ((-52927/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6654988053/200000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-52927/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c254 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-499819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1946673/2500000) (δ := 6311/500000000) (ψ := -540941/500000) 250 220
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t254 : ((-306279411/4882812500 : ℚ) : ℝ) ≤ stT250 254 := by
  have hc : ((-124961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306279411/4882812500 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-124961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c255 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-288637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2732729/5000000) (δ := 793/62500000) (ψ := -540941/500000) 250 221
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t255 : ((-3615347219/100000000000 : ℚ) : ℝ) ≤ stT250 255 := by
  have hc : ((-144331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3615347219/100000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-144331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c256 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((355163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3019271/10000000) (δ := 2503/200000000) (ψ := -540941/500000) 250 221
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t256 : ((355113/16000000 : ℚ) : ℝ) ≤ stT250 256 := by
  have hc : ((355113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355113/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((355113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c257 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((194593/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291323/5000000) (δ := 2503/200000000) (ψ := -540941/500000) 250 221
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t257 : ((60688686453/1000000000000 : ℚ) : ℝ) ≤ stT250 257 := by
  have hc : ((194583/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60688686453/1000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((194583/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c258 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((739939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 922271/5000000) (δ := 793/62500000) (ψ := -540941/500000) 250 221
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t258 : ((115158543627/2500000000000 : ℚ) : ℝ) ≤ stT250 258 := by
  have hc : ((739889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115158543627/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((739889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c259 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-133743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2131177/5000000) (δ := 2503/200000000) (ψ := -540941/500000) 250 221
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t259 : ((-8313495641/1000000000000 : ℚ) : ℝ) ≤ stT250 259 := by
  have hc : ((-133793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8313495641/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-133793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c260 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-890091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3335427/5000000) (δ := 2503/200000000) (ψ := -540941/500000) 250 221
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t260 : ((-276021152267/5000000000000 : ℚ) : ℝ) ≤ stT250 260 := by
  have hc : ((-890141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276021152267/5000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-890141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c261 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-441999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6637859/10000000) (δ := 2519/200000000) (ψ := -540941/500000) 250 222
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t261 : ((-6840155641/125000000000 : ℚ) : ℝ) ≤ stT250 261 := by
  have hc : ((-55253/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6840155641/125000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-55253/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c262 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-127971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4247797/10000000) (δ := 4701/125000000) (ψ := -540941/500000) 250 222
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t262 : ((-79091757863/10000000000000 : ℚ) : ℝ) ≤ stT250 262 := by
  have hc : ((-128021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79091757863/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-128021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c263 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((146781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1866859/10000000) (δ := 2519/200000000) (ψ := -540941/500000) 250 222
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t263 : ((45251407323/1000000000000 : ℚ) : ℝ) ≤ stT250 263 := by
  have hc : ((146771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45251407323/1000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((146771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c264 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((979661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 252539/5000000) (δ := 4701/125000000) (ψ := -540941/500000) 250 222
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t264 : ((602908447227/10000000000000 : ℚ) : ℝ) ≤ stT250 264 := by
  have hc : ((979611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((602908447227/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((979611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c265 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((102759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179251/625000) (δ := 2519/200000000) (ψ := -540941/500000) 250 222
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t265 : ((25246664487/1000000000000 : ℚ) : ℝ) ≤ stT250 265 := by
  have hc : ((205493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25246664487/1000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((205493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c266 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-247587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2611039/5000000) (δ := 197/15625000) (ψ := -540941/500000) 250 222
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t266 : ((-1897760271/62500000000 : ℚ) : ℝ) ≤ stT250 266 := by
  have hc : ((-61903/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1897760271/62500000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-61903/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c267 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-993431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3783633/5000000) (δ := 2519/200000000) (ψ := -540941/500000) 250 222
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t267 : ((-608001430671/10000000000000 : ℚ) : ℝ) ≤ stT250 267 := by
  have hc : ((-993481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608001430671/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-993481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c268 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-682303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290213/500000) (δ := 12503/1000000000) (ψ := -540941/500000) 250 223
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t268 : ((-13025436417/312500000000 : ℚ) : ℝ) ≤ stT250 268 := by
  have hc : ((-682353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13025436417/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-682353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c269 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((179219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347651/1000000) (δ := 12503/1000000000) (ψ := -540941/500000) 250 223
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t269 : ((10924113099/1000000000000 : ℚ) : ℝ) ≤ stT250 269 := by
  have hc : ((179169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10924113099/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((179169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c270 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((894737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231477/2000000) (δ := 12503/1000000000) (ψ := -540941/500000) 250 223
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t270 : ((27224430723/500000000000 : ℚ) : ℝ) ≤ stT250 270 := by
  have hc : ((894687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27224430723/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((894687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c271 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((13992/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1153177/10000000) (δ := 127/10000000) (ψ := -540941/500000) 250 223
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t271 : ((8499049777/156250000000 : ℚ) : ℝ) ≤ stT250 271 := by
  have hc : ((447719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8499049777/156250000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((447719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c272 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((187607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3455177/10000000) (δ := 127/10000000) (ψ := -540941/500000) 250 223
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t272 : ((113723123823/10000000000000 : ℚ) : ℝ) ≤ stT250 272 := by
  have hc : ((187557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113723123823/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((187557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c273 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-6659/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287437/500000) (δ := 12503/1000000000) (ψ := -540941/500000) 250 223
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t273 : ((-2015257933/50000000000 : ℚ) : ℝ) ≤ stT250 273 := by
  have hc : ((-13319/20000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2015257933/50000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-13319/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c274 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-997409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7673973/10000000) (δ := 1261/100000000) (ψ := -540941/500000) 250 224
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t274 : ((-602587923457/10000000000000 : ℚ) : ℝ) ≤ stT250 274 := by
  have hc : ((-997459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-602587923457/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-997459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c275 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-110951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5397161/10000000) (δ := 12593/1000000000) (ψ := -540941/500000) 250 224
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t275 : ((-66912035103/2000000000000 : ℚ) : ℝ) ≤ stT250 275 := by
  have hc : ((-110961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66912035103/2000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-110961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c276 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((15699/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391067/1250000) (δ := 12593/1000000000) (ψ := -540941/500000) 250 224
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t276 : ((18896357097/1000000000000 : ℚ) : ℝ) ≤ stT250 276 := by
  have hc : ((31393/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18896357097/1000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((31393/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c277 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((235079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434049/5000000) (δ := 1261/100000000) (ψ := -540941/500000) 250 224
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t277 : ((282475181853/5000000000000 : ℚ) : ℝ) ≤ stT250 277 := by
  have hc : ((470133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282475181853/5000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((470133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c278 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((170121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173019/1250000) (δ := 1261/100000000) (ψ := -540941/500000) 250 224
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t278 : ((1275322167/25000000000 : ℚ) : ℝ) ≤ stT250 278 := by
  have hc : ((170111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1275322167/25000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((170111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c279 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((119201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3628277/10000000) (δ := 1261/100000000) (ψ := -540941/500000) 250 224
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t279 : ((17833449321/2500000000000 : ℚ) : ℝ) ≤ stT250 279 := by
  have hc : ((119151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17833449321/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((119151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c280 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-174927/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 366529/625000) (δ := 12593/1000000000) (ψ := -540941/500000) 250 224
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t280 : ((-41818587717/1000000000000 : ℚ) : ℝ) ≤ stT250 280 := by
  have hc : ((-349879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41818587717/1000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-349879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c281 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-995449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3807687/5000000) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t281 : ((-11877298569/200000000000 : ℚ) : ℝ) ≤ stT250 281 := by
  have hc : ((-995499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11877298569/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-995499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c282 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-554077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348781/2500000) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t282 : ((-82494548871/2500000000000 : ℚ) : ℝ) ≤ stT250 282 := by
  have hc : ((-554127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82494548871/2500000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-554127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c283 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((293319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3182749/10000000) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t283 : ((87165118911/5000000000000 : ℚ) : ℝ) ≤ stT250 283 := by
  have hc : ((293269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87165118911/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((293269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c284 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((924433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244531/2500000) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t284 : ((54851962837/1000000000000 : ℚ) : ℝ) ≤ stT250 284 := by
  have hc : ((924383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54851962837/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((924383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c285 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((441759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9521/78125) (δ := 6343/500000000) (ψ := -540941/500000) 250 225
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t285 : ((32707531429/625000000000 : ℚ) : ℝ) ≤ stT250 285 := by
  have hc : ((220867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32707531429/625000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((220867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c286 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((206157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 851969/2500000) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t286 : ((7617096399/625000000000 : ℚ) : ℝ) ≤ stT250 286 := by
  have hc : ((206107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7617096399/625000000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((206107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c287 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-617023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43667/78125) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t287 : ((-182123542293/5000000000000 : ℚ) : ℝ) ≤ stT250 287 := by
  have hc : ((-617073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182123542293/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-617073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c288 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-499671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7763251/10000000) (δ := 12517/1000000000) (ψ := -540941/500000) 250 225
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t288 : ((-2300381767/39062500000 : ℚ) : ℝ) ≤ stT250 288 := by
  have hc : ((-31231/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2300381767/39062500000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-31231/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c289 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-134937/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5778337/10000000) (δ := 789/62500000) (ψ := -540941/500000) 250 226
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t289 : ((-19845170873/500000000000 : ℚ) : ℝ) ≤ stT250 289 := by
  have hc : ((-134947/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19845170873/500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-134947/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c290 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((61363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18097/50000) (δ := 12579/1000000000) (ψ := -540941/500000) 250 226
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t290 : ((900472509/125000000000 : ℚ) : ℝ) ≤ stT250 290 := by
  have hc : ((30669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((900472509/125000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((30669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c291 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((104063/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -733981/5000000) (δ := 789/62500000) (ψ := -540941/500000) 250 226
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t291 : ((24399642967/500000000000 : ℚ) : ℝ) ≤ stT250 291 := by
  have hc : ((416227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24399642967/500000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((416227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c292 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((963647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676163/10000000) (δ := 789/62500000) (ψ := -540941/500000) 250 226
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t292 : ((112780356477/2000000000000 : ℚ) : ℝ) ≤ stT250 292 := by
  have hc : ((963597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112780356477/2000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((963597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c293 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((431027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2812913/10000000) (δ := 789/62500000) (ψ := -540941/500000) 250 226
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t293 : ((125889674631/5000000000000 : ℚ) : ℝ) ≤ stT250 293 := by
  have hc : ((430977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125889674631/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((430977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c294 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-39507/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98847/200000) (δ := 12579/1000000000) (ψ := -540941/500000) 250 226
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t294 : ((-720121017/31250000000 : ℚ) : ℝ) ≤ stT250 294 := by
  have hc : ((-4939/12500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-720121017/31250000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-4939/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c295 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-950563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35323/50000) (δ := 12579/1000000000) (ψ := -540941/500000) 250 226
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t295 : ((-553468752699/10000000000000 : ℚ) : ℝ) ≤ stT250 295 := by
  have hc : ((-950613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553468752699/10000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-950613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c296 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-862669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6528301/10000000) (δ := 99/7812500) (ψ := -540941/500000) 250 227
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t296 : ((-501445928841/10000000000000 : ℚ) : ℝ) ≤ stT250 296 := by
  have hc : ((-862719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501445928841/10000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-862719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c297 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-19607/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4420363/10000000) (δ := 12531/1000000000) (ψ := -540941/500000) 250 227
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t297 : ((-2845009877/250000000000 : ℚ) : ℝ) ≤ stT250 297 := by
  have hc : ((-4903/25000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2845009877/250000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-4903/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c298 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((29979/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2319551/10000000) (δ := 99/7812500) (ψ := -540941/500000) 250 227
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t298 : ((8682453413/250000000000 : ℚ) : ℝ) ≤ stT250 298 := by
  have hc : ((59953/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8682453413/250000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((59953/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c299 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((497963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112869/5000000) (δ := 12531/1000000000) (ψ := -540941/500000) 250 227
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t299 : ((71991129133/1250000000000 : ℚ) : ℝ) ≤ stT250 299 := by
  have hc : ((248969/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71991129133/1250000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((248969/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c300 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((367737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 930537/5000000) (δ := 99/7812500) (ψ := -540941/500000) 250 227
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t300 : ((132686577/3125000000 : ℚ) : ℝ) ≤ stT250 300 := by
  have hc : ((11491/15625 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132686577/3125000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((11491/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c301 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-5583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3940949/10000000) (δ := 99/7812500) (ψ := -540941/500000) 250 227
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t301 : ((-3246810503/10000000000000 : ℚ) : ℝ) ≤ stT250 301 := by
  have hc : ((-5633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3246810503/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-5633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c302 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-741151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6013949/10000000) (δ := 99/7812500) (ψ := -540941/500000) 250 227
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t302 : ((-106628434659/2500000000000 : ℚ) : ℝ) ≤ stT250 302 := by
  have hc : ((-741201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106628434659/2500000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-741201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c303 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-995913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7627889/10000000) (δ := 2513/200000000) (ψ := -540941/500000) 250 228
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t303 : ((-114433160811/2000000000000 : ℚ) : ℝ) ≤ stT250 303 := by
  have hc : ((-995963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114433160811/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-995963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c304 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-305227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87009/156250) (δ := 6319/500000000) (ψ := -540941/500000) 250 228
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t304 : ((-2188427901/62500000000 : ℚ) : ℝ) ≤ stT250 304 := by
  have hc : ((-76313/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2188427901/62500000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-76313/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c305 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((163627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -879019/2500000) (δ := 6319/500000000) (ψ := -540941/500000) 250 228
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t305 : ((46831931523/5000000000000 : ℚ) : ℝ) ≤ stT250 305 := by
  have hc : ((163577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46831931523/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((163577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c306 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((832007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470201/10000000) (δ := 6319/500000000) (ψ := -540941/500000) 250 228
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t306 : ((475597370577/10000000000000 : ℚ) : ℝ) ≤ stT250 306 := by
  have hc : ((831957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475597370577/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((831957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c307 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((487109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142231/2500000) (δ := 6319/500000000) (ψ := -540941/500000) 250 228
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t307 : ((6949836283/125000000000 : ℚ) : ℝ) ≤ stT250 307 := by
  have hc : ((121771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6949836283/125000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((121771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c308 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((505729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162589/625000) (δ := 6319/500000000) (ψ := -540941/500000) 250 228
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t308 : ((144068452779/5000000000000 : ℚ) : ℝ) ≤ stT250 308 := by
  have hc : ((505679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144068452779/5000000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((505679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c309 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-138249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4627361/10000000) (δ := 2513/200000000) (ψ := -540941/500000) 250 228
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t309 : ((-39330725697/2500000000000 : ℚ) : ℝ) ≤ stT250 309 := by
  have hc : ((-69137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39330725697/2500000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-69137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c310 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-885653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 415421/625000) (δ := 2513/200000000) (ψ := -540941/500000) 250 228
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t310 : ((-251522823643/5000000000000 : ℚ) : ℝ) ≤ stT250 310 := by
  have hc : ((-885703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251522823643/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-885703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c311 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-948517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -704829/1000000) (δ := 12657/1000000000) (ψ := -540941/500000) 250 229
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t311 : ((-67235377527/1250000000000 : ℚ) : ℝ) ≤ stT250 311 := by
  have hc : ((-948567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67235377527/1250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-948567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c312 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-431333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1008383/2000000) (δ := 12657/1000000000) (ψ := -540941/500000) 250 229
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t312 : ((-244222740237/10000000000000 : ℚ) : ℝ) ≤ stT250 312 := by
  have hc : ((-431383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244222740237/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-431383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c313 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((346681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608383/2000000) (δ := 12657/1000000000) (ψ := -540941/500000) 250 229
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t313 : ((195927280023/10000000000000 : ℚ) : ℝ) ≤ stT250 313 := by
  have hc : ((346631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195927280023/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((346631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c314 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((114171/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104829/1000000) (δ := 12657/1000000000) (ψ := -540941/500000) 250 229
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t314 : ((64426821697/1250000000000 : ℚ) : ℝ) ≤ stT250 314 := by
  have hc : ((456659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64426821697/1250000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((456659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c315 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((232571/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 939023/10000000) (δ := 6273/500000000) (ψ := -540941/500000) 250 229
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t315 : ((65515915503/1250000000000 : ℚ) : ℝ) ≤ stT250 315 := by
  have hc : ((465117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65515915503/1250000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((465117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c316 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((24499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2920023/10000000) (δ := 6273/500000000) (ψ := -540941/500000) 250 229
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t316 : ((110239864081/5000000000000 : ℚ) : ℝ) ≤ stT250 316 := by
  have hc : ((195967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110239864081/5000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((195967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c317 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-377493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489471/1000000) (δ := 12657/1000000000) (ψ := -540941/500000) 250 229
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t317 : ((-26506161401/1250000000000 : ℚ) : ℝ) ≤ stT250 317 := by
  have hc : ((-377543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26506161401/1250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-377543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c318 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-230623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 686321/1000000) (δ := 12657/1000000000) (ψ := -540941/500000) 250 229
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t318 : ((-258668322483/5000000000000 : ℚ) : ℝ) ≤ stT250 318 := by
  have hc : ((-461271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258668322483/5000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-461271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c319 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-37017/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3441189/5000000) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t319 : ((-20726678967/400000000000 : ℚ) : ℝ) ≤ stT250 319 := by
  have hc : ((-37019/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20726678967/400000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-37019/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c320 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-194573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4926253/10000000) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t320 : ((-54391795083/2500000000000 : ℚ) : ℝ) ≤ stT250 320 := by
  have hc : ((-97299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54391795083/2500000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-97299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c321 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((371241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23251/78125) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t321 : ((41435680139/2000000000000 : ℚ) : ℝ) ≤ stT250 321 := by
  have hc : ((371191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41435680139/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((371191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c322 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((915981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16127/156250) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t322 : ((255214097909/5000000000000 : ℚ) : ℝ) ≤ stT250 322 := by
  have hc : ((915931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255214097909/5000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((915931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c323 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((935067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56617/625000) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t323 : ((260128274519/5000000000000 : ℚ) : ℝ) ≤ stT250 323 := by
  have hc : ((935017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260128274519/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((935017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c324 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((210999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177367/625000) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t324 : ((11720766057/500000000000 : ℚ) : ℝ) ≤ stT250 324 := by
  have hc : ((105487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11720766057/500000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((105487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c325 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-65707/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148871/312500) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t325 : ((-36453285617/2000000000000 : ℚ) : ℝ) ≤ stT250 325 := by
  have hc : ((-65717/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36453285617/2000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-65717/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c326 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-35699/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6683997/10000000) (δ := 251/20000000) (ψ := -540941/500000) 250 230
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t326 : ((-19772963149/400000000000 : ℚ) : ℝ) ≤ stT250 326 := by
  have hc : ((-35701/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19772963149/400000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-35701/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c327 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-239003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1777429/2500000) (δ := 157/12500000) (ψ := -540941/500000) 250 231
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t327 : ((-132176049531/2500000000000 : ℚ) : ℝ) ≤ stT250 327 := by
  have hc : ((-478031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132176049531/2500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-478031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c328 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-487929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5201279/10000000) (δ := 12643/1000000000) (ψ := -540941/500000) 250 231
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t328 : ((-134720754341/5000000000000 : ℚ) : ℝ) ≤ stT250 328 := by
  have hc : ((-487979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134720754341/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-487979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c329 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((248673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -824679/2500000) (δ := 157/12500000) (ψ := -540941/500000) 250 231
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t329 : ((137070086491/10000000000000 : ℚ) : ℝ) ≤ stT250 329 := by
  have hc : ((248623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137070086491/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((248623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c330 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((16937/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87619/625000) (δ := 12643/1000000000) (ψ := -540941/500000) 250 231
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t330 : ((1165368277/25000000000 : ℚ) : ℝ) ≤ stT250 330 := by
  have hc : ((2117/2500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1165368277/25000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((2117/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c331 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((980919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489159/10000000) (δ := 157/12500000) (ψ := -540941/500000) 250 231
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t331 : ((539133664981/10000000000000 : ℚ) : ℝ) ≤ stT250 331 := by
  have hc : ((980869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539133664981/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((980869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c332 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((116367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187267/5000000) (δ := 157/12500000) (ψ := -540941/500000) 250 231
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t332 : ((63859165097/2000000000000 : ℚ) : ℝ) ≤ stT250 332 := by
  have hc : ((116357/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63859165097/2000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((116357/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c333 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-130519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4254221/10000000) (δ := 12643/1000000000) (ψ := -540941/500000) 250 231
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t333 : ((-71551420293/10000000000000 : ℚ) : ℝ) ≤ stT250 333 := by
  have hc : ((-130569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71551420293/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-130569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c334 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-192767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1532071/2500000) (δ := 157/12500000) (ψ := -540941/500000) 250 231
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t334 : ((-26371078923/625000000000 : ℚ) : ℝ) ≤ stT250 334 := by
  have hc : ((-385559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26371078923/625000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-385559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c335 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-998369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7711179/10000000) (δ := 12667/1000000000) (ψ := -540941/500000) 250 232
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t335 : ((-545495206421/10000000000000 : ℚ) : ℝ) ≤ stT250 335 := by
  have hc : ((-998419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-545495206421/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-998419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c336 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-173769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -365519/625000) (δ := 12667/1000000000) (ψ := -540941/500000) 250 232
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t336 : ((-37922251367/1000000000000 : ℚ) : ℝ) ≤ stT250 336 := by
  have hc : ((-347563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37922251367/1000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-347563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c337 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-6393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3990929/10000000) (δ := 12667/1000000000) (ψ := -540941/500000) 250 232
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t337 : ((-1395720017/1000000000000 : ℚ) : ℝ) ≤ stT250 337 := by
  have hc : ((-12811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1395720017/1000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-12811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c338 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((65573/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2139117/10000000) (δ := 1567/125000000) (ψ := -540941/500000) 250 232
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t338 : ((139313559/3906250000 : ℚ) : ℝ) ≤ stT250 338 := by
  have hc : ((2049/3125 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139313559/3906250000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((2049/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c339 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((198631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292679/10000000) (δ := 12667/1000000000) (ψ := -540941/500000) 250 232
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t339 : ((172601649/3200000000 : ℚ) : ℝ) ≤ stT250 339 := by
  have hc : ((198621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172601649/3200000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((198621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c340 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((814283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774129/5000000) (δ := 1567/125000000) (ψ := -540941/500000) 250 232
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t340 : ((220789862979/5000000000000 : ℚ) : ℝ) ≤ stT250 340 := by
  have hc : ((814233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220789862979/5000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((814233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c341 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((215587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1691879/5000000) (δ := 1567/125000000) (ψ := -540941/500000) 250 232
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t341 : ((11671975161/1000000000000 : ℚ) : ℝ) ≤ stT250 341 := by
  have hc : ((215537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11671975161/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((215537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c342 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-98469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2606973/5000000) (δ := 12667/1000000000) (ψ := -540941/500000) 250 232
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t342 : ((-53251435981/2000000000000 : ℚ) : ℝ) ≤ stT250 342 := by
  have hc : ((-98479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53251435981/2000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-98479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c343 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-473651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3519379/5000000) (δ := 1567/125000000) (ψ := -540941/500000) 250 232
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t343 : ((-1278806781/25000000000 : ℚ) : ℝ) ≤ stT250 343 := by
  have hc : ((-118419/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1278806781/25000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-118419/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c344 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-920393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1369941/2000000) (δ := 6287/500000000) (ψ := -540941/500000) 250 233
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t344 : ((-124067432413/2500000000000 : ℚ) : ℝ) ≤ stT250 344 := by
  have hc : ((-920443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124067432413/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-920443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c345 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-429/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1007091/2000000) (δ := 6287/500000000) (ψ := -540941/500000) 250 233
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t345 : ((-2309927971/100000000000 : ℚ) : ℝ) ≤ stT250 345 := by
  have hc : ((-8581/20000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2309927971/100000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-8581/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c346 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((276537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1613259/5000000) (δ := 12629/1000000000) (ψ := -540941/500000) 250 233
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t346 : ((148640240661/10000000000000 : ℚ) : ℝ) ≤ stT250 346 := by
  have hc : ((276487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148640240661/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((276487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c347 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((421191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88923/625000) (δ := 12629/1000000000) (ψ := -540941/500000) 250 233
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t347 : ((28261712681/625000000000 : ℚ) : ℝ) ≤ stT250 347 := by
  have hc : ((210583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28261712681/625000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((210583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c348 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((247181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75159/2000000) (δ := 6287/500000000) (ψ := -540941/500000) 250 233
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t348 : ((33124039359/625000000000 : ℚ) : ℝ) ≤ stT250 348 := by
  have hc : ((494337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33124039359/625000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((494337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c349 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((161647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135577/625000) (δ := 12629/1000000000) (ψ := -540941/500000) 250 233
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t349 : ((173041693203/5000000000000 : ℚ) : ℝ) ≤ stT250 349 := by
  have hc : ((323269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173041693203/5000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((323269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c350 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-3049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1978741/5000000) (δ := 12629/1000000000) (ψ := -540941/500000) 250 233
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t350 : ((-3272884329/5000000000000 : ℚ) : ℝ) ≤ stT250 350 := by
  have hc : ((-6123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3272884329/5000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-6123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c351 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-10367/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 574067/1000000) (δ := 6287/500000000) (ψ := -540941/500000) 250 233
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t351 : ((-177085353209/5000000000000 : ℚ) : ℝ) ≤ stT250 351 := by
  have hc : ((-331769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177085353209/5000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-331769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c352 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-495511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1879683/2500000) (δ := 12629/1000000000) (ψ := -540941/500000) 250 233
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t352 : ((-8253802471/156250000000 : ℚ) : ℝ) ≤ stT250 352 := by
  have hc : ((-30971/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8253802471/156250000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-30971/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c353 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-209781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -802021/1250000) (δ := 6341/500000000) (ψ := -540941/500000) 250 234
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t353 : ((-223323921989/5000000000000 : ℚ) : ℝ) ≤ stT250 353 := by
  have hc : ((-419587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223323921989/5000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-419587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c354 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-284463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2324053/5000000) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t354 : ((-30243447387/2000000000000 : ℚ) : ℝ) ≤ stT250 354 := by
  have hc : ((-284513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30243447387/2000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-284513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c355 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((202397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1442553/5000000) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t355 : ((3356491399/156250000000 : ℚ) : ℝ) ≤ stT250 355 := by
  have hc : ((50593/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3356491399/156250000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((50593/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c356 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((450051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1126981/10000000) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t356 : ((59628219987/1250000000000 : ℚ) : ℝ) ≤ stT250 356 := by
  have hc : ((225013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59628219987/1250000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((225013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c357 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((968799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19567/312500) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t357 : ((64089527593/1250000000000 : ℚ) : ℝ) ≤ stT250 357 := by
  have hc : ((968749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64089527593/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((968749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c358 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((14547/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1187197/5000000) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t358 : ((7687661607/250000000000 : ℚ) : ℝ) ≤ stT250 358 := by
  have hc : ((58183/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7687661607/250000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((58183/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c359 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-76237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4117769/10000000) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t359 : ((-2013137643/500000000000 : ℚ) : ℝ) ≤ stT250 359 := by
  have hc : ((-76287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2013137643/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-76287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c360 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-697381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1464083/2500000) (δ := 6341/500000000) (ψ := -540941/500000) 250 234
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t360 : ((-367578916257/10000000000000 : ℚ) : ℝ) ≤ stT250 360 := by
  have hc : ((-697431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367578916257/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-697431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c361 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-994431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7590019/10000000) (δ := 12521/1000000000) (ψ := -540941/500000) 250 234
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t361 : ((-130852815499/2500000000000 : ℚ) : ℝ) ≤ stT250 361 := by
  have hc : ((-994481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130852815499/2500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-994481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c362 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-166633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6389007/10000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 235
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t362 : ((-87585727727/2000000000000 : ℚ) : ℝ) ≤ stT250 362 := by
  have hc : ((-166643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87585727727/2000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-166643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c363 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-29089/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2332441/5000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 235
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t363 : ((-119299947/7812500000 : ℚ) : ℝ) ≤ stT250 363 := by
  have hc : ((-14547/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119299947/7812500000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-14547/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c364 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((191293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2945507/10000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 235
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t364 : ((12531449007/625000000000 : ℚ) : ℝ) ≤ stT250 364 := by
  have hc : ((47817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12531449007/625000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((47817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c365 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((176247/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1230819/10000000) (δ := 12589/1000000000) (ψ := -540941/500000) 250 235
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t365 : ((92246499251/2000000000000 : ℚ) : ℝ) ≤ stT250 365 := by
  have hc : ((176237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92246499251/2000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((176237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c366 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((981687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 479181/10000000) (δ := 12589/1000000000) (ψ := -540941/500000) 250 235
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t366 : ((128277378249/2500000000000 : ℚ) : ℝ) ≤ stT250 366 := by
  have hc : ((981637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128277378249/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((981637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c367 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((2006/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2184493/10000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 235
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t367 : ((6701058613/200000000000 : ℚ) : ℝ) ≤ stT250 367 := by
  have hc : ((64187/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6701058613/200000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((64187/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c368 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((16723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3885181/10000000) (δ := 12589/1000000000) (ψ := -540941/500000) 250 235
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t368 : ((4345700739/5000000000000 : ℚ) : ℝ) ≤ stT250 368 := by
  have hc : ((16673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4345700739/5000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((16673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c369 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-30723/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5581243/10000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 235
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t369 : ((-1599508079/50000000000 : ℚ) : ℝ) ≤ stT250 369 := by
  have hc : ((-61451/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1599508079/50000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-61451/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c370 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-486547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7272743/10000000) (δ := 6307/500000000) (ψ := -540941/500000) 250 235
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t370 : ((-15809819067/312500000000 : ℚ) : ℝ) ≤ stT250 370 := by
  have hc : ((-121643/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15809819067/312500000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-121643/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c371 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-903789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1349669/2000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 236
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t371 : ((-18770024513/400000000000 : ℚ) : ℝ) ≤ stT250 371 := by
  have hc : ((-903839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18770024513/400000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-903839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c372 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-219997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -506597/1000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 236
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t372 : ((-14259515809/625000000000 : ℚ) : ℝ) ≤ stT250 372 := by
  have hc : ((-110011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14259515809/625000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-110011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c373 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((213893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677619/2000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 236
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t373 : ((5536181427/500000000000 : ℚ) : ℝ) ≤ stT250 373 := by
  have hc : ((213843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5536181427/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((213843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c374 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((773841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857391/5000000) (δ := 1587/125000000) (ψ := -540941/500000) 250 236
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t374 : ((400117266817/10000000000000 : ℚ) : ℝ) ≤ stT250 374 := by
  have hc : ((773791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400117266817/10000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((773791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c375 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((124979/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9169/2000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 236
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t375 : ((258142212727/5000000000000 : ℚ) : ℝ) ≤ stT250 375 := by
  have hc : ((499891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258142212727/5000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((499891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c376 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((12463/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1618593/10000000) (δ := 1587/125000000) (ψ := -540941/500000) 250 236
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t376 : ((20566050661/500000000000 : ℚ) : ℝ) ≤ stT250 376 := by
  have hc : ((398791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20566050661/500000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((398791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c377 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((256461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3278593/10000000) (δ := 1587/125000000) (ψ := -540941/500000) 250 236
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t377 : ((66029165843/5000000000000 : ℚ) : ℝ) ≤ stT250 377 := by
  have hc : ((256411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66029165843/5000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((256411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c378 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-392079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2467109/5000000) (δ := 1587/125000000) (ψ := -540941/500000) 250 236
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t378 : ((-40337918101/2000000000000 : ℚ) : ℝ) ≤ stT250 378 := by
  have hc : ((-392129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40337918101/2000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-392129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c379 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-43701/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658553/1000000) (δ := 12507/1000000000) (ψ := -540941/500000) 250 236
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t379 : ((-22449002031/500000000000 : ℚ) : ℝ) ≤ stT250 379 := by
  have hc : ((-87407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22449002031/500000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-87407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c380 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-494283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3737779/5000000) (δ := 12603/1000000000) (ψ := -540941/500000) 250 237
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t380 : ((-6339376523/125000000000 : ℚ) : ℝ) ≤ stT250 380 := by
  have hc : ((-123577/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6339376523/125000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-123577/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c381 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-690661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1458249/2500000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t381 : ((-88465574169/2500000000000 : ℚ) : ℝ) ≤ stT250 381 := by
  have hc : ((-690711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88465574169/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-690711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c382 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-13359/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4194683/10000000) (δ := 12603/1000000000) (ψ := -540941/500000) 250 237
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t382 : ((-5470610669/1000000000000 : ℚ) : ℝ) ≤ stT250 382 := by
  have hc : ((-53461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5470610669/1000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-53461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c383 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((259849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1280373/5000000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t383 : ((32413044/1220703125 : ℚ) : ℝ) ≤ stT250 383 := by
  have hc : ((16239/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32413044/1220703125 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((16239/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c384 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((931457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232749/2500000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t384 : ((47530630617/1000000000000 : ℚ) : ℝ) ≤ stT250 384 := by
  have hc : ((931407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47530630617/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((931407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c385 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((961661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86813/1250000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t385 : ((490082161317/10000000000000 : ℚ) : ℝ) ≤ stT250 385 := by
  have hc : ((961611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((490082161317/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((961611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c386 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((120159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1157877/5000000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t386 : ((30577079457/1000000000000 : ℚ) : ℝ) ≤ stT250 386 := by
  have hc : ((120149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30577079457/1000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((120149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c387 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-233/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3932817/10000000) (δ := 12603/1000000000) (ψ := -540941/500000) 250 237
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t387 : ((-60491151/500000000000 : ℚ) : ℝ) ≤ stT250 387 := by
  have hc : ((-119/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60491151/500000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-119/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c388 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-603199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2772877/5000000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t388 : ((-153126916413/5000000000000 : ℚ) : ℝ) ≤ stT250 388 := by
  have hc : ((-603249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153126916413/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-603249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c389 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-961113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 894313/1250000) (δ := 63/5000000) (ψ := -540941/500000) 250 237
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t389 : ((-487329825423/10000000000000 : ℚ) : ℝ) ≤ stT250 389 := by
  have hc : ((-961163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-487329825423/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-961163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c390 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-935169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3474417/5000000) (δ := 1251/100000000) (ψ := -540941/500000) 250 238
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t390 : ((-47356684503/1000000000000 : ℚ) : ℝ) ≤ stT250 390 := by
  have hc : ((-935219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47356684503/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-935219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c391 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-673/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2674167/5000000) (δ := 1251/100000000) (ψ := -540941/500000) 250 238
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t391 : ((-2723060109/100000000000 : ℚ) : ℝ) ≤ stT250 391 := by
  have hc : ((-10769/20000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2723060109/100000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-10769/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c392 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((3499/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3751897/10000000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 238
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t392 : ((882999117/250000000000 : ℚ) : ℝ) ≤ stT250 392 := by
  have hc : ((6993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((882999117/250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((6993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c393 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((324773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1079761/5000000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 238
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t393 : ((40953401971/1250000000000 : ℚ) : ℝ) ≤ stT250 393 := by
  have hc : ((81187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40953401971/1250000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((81187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c394 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((974011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571209/10000000) (δ := 1251/100000000) (ψ := -540941/500000) 250 238
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t394 : ((30667110007/625000000000 : ℚ) : ℝ) ≤ stT250 394 := by
  have hc : ((973961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30667110007/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((973961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c395 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((919017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1013041/10000000) (δ := 1251/100000000) (ψ := -540941/500000) 250 238
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t395 : ((231190960959/5000000000000 : ℚ) : ℝ) ≤ stT250 395 := by
  have hc : ((918967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231190960959/5000000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((918967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c396 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((508511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2593353/10000000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 238
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t396 : ((127755402399/5000000000000 : ℚ) : ℝ) ≤ stT250 396 := by
  have hc : ((508461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127755402399/5000000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((508461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c397 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-96893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4169603/10000000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 238
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t397 : ((-24327167249/5000000000000 : ℚ) : ℝ) ≤ stT250 397 := by
  have hc : ((-96943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24327167249/5000000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-96943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c398 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-16597/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2870989/5000000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 238
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t398 : ((-6655964643/200000000000 : ℚ) : ℝ) ≤ stT250 398 := by
  have hc : ((-66393/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6655964643/200000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-66393/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c399 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-19529/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7310353/10000000) (δ := 12693/1000000000) (ψ := -540941/500000) 250 238
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t399 : ((-977724531/20000000000 : ℚ) : ℝ) ≤ stT250 399 := by
  have hc : ((-1953/2000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-977724531/20000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-1953/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c400 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-229447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1708293/2500000) (δ := 12617/1000000000) (ψ := -540941/500000) 250 239
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t400 : ((-229459958919/5000000000000 : ℚ) : ℝ) ≤ stT250 400 := by
  have hc : ((-458919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229459958919/5000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-458919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c401 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-64079/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -527261/1000000) (δ := 6293/500000000) (ψ := -540941/500000) 250 239
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t401 : ((-128010799557/5000000000000 : ℚ) : ℝ) ≤ stT250 401 := by
  have hc : ((-256341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128010799557/5000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-256341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c402 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((42151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -743197/2000000) (δ := 6293/500000000) (ψ := -540941/500000) 250 239
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t402 : ((5252627751/1250000000000 : ℚ) : ℝ) ≤ stT250 402 := by
  have hc : ((21063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5252627751/1250000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((21063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c403 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((162109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -540793/2500000) (δ := 12617/1000000000) (ψ := -540941/500000) 250 239
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t403 : ((32298376011/1000000000000 : ℚ) : ℝ) ≤ stT250 403 := by
  have hc : ((324193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32298376011/1000000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((324193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c404 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((969969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122847/2000000) (δ := 6293/500000000) (ψ := -540941/500000) 250 239
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t404 : ((241276080521/5000000000000 : ℚ) : ℝ) ≤ stT250 404 := by
  have hc : ((969919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241276080521/5000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((969919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c405 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((931473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93089/1000000) (δ := 6293/500000000) (ψ := -540941/500000) 250 239
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t405 : ((462826882969/10000000000000 : ℚ) : ℝ) ≤ stT250 405 := by
  have hc : ((931423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462826882969/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((931423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c406 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((4397/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2472203/10000000) (δ := 12617/1000000000) (ψ := -540941/500000) 250 239
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t406 : ((10909965053/400000000000 : ℚ) : ℝ) ≤ stT250 406 := by
  have hc : ((21983/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10909965053/400000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((21983/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c407 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-33079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4009703/10000000) (δ := 12617/1000000000) (ψ := -540941/500000) 250 239
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t407 : ((-8210724489/5000000000000 : ℚ) : ℝ) ≤ stT250 407 := by
  have hc : ((-33129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8210724489/5000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-33129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c408 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-18827/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5543453/10000000) (δ := 12617/1000000000) (ψ := -540941/500000) 250 239
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t408 : ((-74572254009/2500000000000 : ℚ) : ℝ) ≤ stT250 408 := by
  have hc : ((-301257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74572254009/2500000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-301257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c409 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-951657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7073453/10000000) (δ := 12617/1000000000) (ψ := -540941/500000) 250 239
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t409 : ((-470589608583/10000000000000 : ℚ) : ℝ) ≤ stT250 409 := by
  have hc : ((-951707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470589608583/10000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-951707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c410 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-955841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7108261/10000000) (δ := 6339/500000000) (ψ := -540941/500000) 250 240
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t410 : ((-94416221743/2000000000000 : ℚ) : ℝ) ≤ stT250 410 := by
  have hc : ((-955891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94416221743/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-955891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c411 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-123173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2792849/5000000) (δ := 501/40000000) (ψ := -540941/500000) 250 240
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t411 : ((-3797608707/125000000000 : ℚ) : ℝ) ≤ stT250 411 := by
  have hc : ((-123183/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3797608707/125000000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-123183/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c412 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-55929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2033443/5000000) (δ := 6339/500000000) (ψ := -540941/500000) 250 240
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t412 : ((-5515778807/2000000000000 : ℚ) : ℝ) ≤ stT250 412 := by
  have hc : ((-55979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5515778807/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-55979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c413 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((261383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2551761/10000000) (δ := 6339/500000000) (ψ := -540941/500000) 250 240
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t413 : ((64302823493/2500000000000 : ℚ) : ℝ) ≤ stT250 413 := by
  have hc : ((130679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64302823493/2500000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((130679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c414 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((91467/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1040261/10000000) (δ := 6339/500000000) (ψ := -540941/500000) 250 240
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t414 : ((22475551763/500000000000 : ℚ) : ℝ) ≤ stT250 414 := by
  have hc : ((45731/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22475551763/500000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((45731/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c415 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((491279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233807/5000000) (δ := 6339/500000000) (ψ := -540941/500000) 250 240
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t415 : ((188395909/3906250000 : ℚ) : ℝ) ≤ stT250 415 := by
  have hc : ((245627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188395909/3906250000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((245627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c416 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((704753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 985901/5000000) (δ := 501/40000000) (ψ := -540941/500000) 250 240
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t416 : ((34550883387/1000000000000 : ℚ) : ℝ) ≤ stT250 416 := by
  have hc : ((704703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34550883387/1000000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((704703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c417 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((7233/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3472427/10000000) (δ := 501/40000000) (ψ := -540941/500000) 250 240
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t417 : ((1770517581/200000000000 : ℚ) : ℝ) ≤ stT250 417 := by
  have hc : ((7231/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1770517581/200000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((7231/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c418 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-101249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4969427/10000000) (δ := 501/40000000) (ψ := -540941/500000) 250 240
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t418 : ((-24764309917/1250000000000 : ℚ) : ℝ) ≤ stT250 418 := by
  have hc : ((-202523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24764309917/1250000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-202523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c419 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-849137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403929/625000) (δ := 6339/500000000) (ψ := -540941/500000) 250 240
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t419 : ((-103713755871/2500000000000 : ℚ) : ℝ) ≤ stT250 419 := by
  have hc : ((-849187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103713755871/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-849187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c420 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-49961/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -969403/1250000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t420 : ((-48759479577/1000000000000 : ℚ) : ℝ) ≤ stT250 420 := by
  have hc : ((-99927/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48759479577/1000000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-99927/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c421 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-50353/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6268911/10000000) (δ := 1579/125000000) (ψ := -540941/500000) 250 241
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t421 : ((-196336919979/5000000000000 : ℚ) : ℝ) ≤ stT250 421 := by
  have hc : ((-402849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196336919979/5000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-402849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c422 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-8423/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4786099/10000000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t422 : ((-16403463721/1000000000000 : ℚ) : ℝ) ≤ stT250 422 := by
  have hc : ((-33697/100000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16403463721/1000000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-33697/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c423 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((245521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3306849/10000000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t423 : ((14918990967/1250000000000 : ℚ) : ℝ) ≤ stT250 423 := by
  have hc : ((245471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14918990967/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((245471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c424 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((371781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -457759/2500000) (δ := 1579/125000000) (ψ := -540941/500000) 250 241
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t424 : ((22567540919/625000000000 : ℚ) : ℝ) ≤ stT250 424 := by
  have hc : ((92939/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22567540919/625000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((92939/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c425 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((989723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89681/2500000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t425 : ((480061671783/10000000000000 : ℚ) : ℝ) ≤ stT250 425 := by
  have hc : ((989673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480061671783/10000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((989673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c426 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((180603/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1110151/10000000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t426 : ((87497489093/2000000000000 : ℚ) : ℝ) ≤ stT250 426 := by
  have hc : ((180593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87497489093/2000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((180593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c427 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((514617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2575589/10000000) (δ := 1579/125000000) (ψ := -540941/500000) 250 241
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t427 : ((249015952011/10000000000000 : ℚ) : ℝ) ≤ stT250 427 := by
  have hc : ((514567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249015952011/10000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((514567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c428 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-221/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2018763/5000000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t428 : ((-85556313/40000000000 : ℚ) : ℝ) ≤ stT250 428 := by
  have hc : ((-177/4000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85556313/40000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-177/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c429 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-73407/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5496151/10000000) (δ := 12571/1000000000) (ψ := -540941/500000) 250 241
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t429 : ((-28355427333/1000000000000 : ℚ) : ℝ) ≤ stT250 429 := by
  have hc : ((-293653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28355427333/1000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-293653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c430 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-233881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6951339/10000000) (δ := 1579/125000000) (ψ := -540941/500000) 250 241
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t430 : ((-225587006241/5000000000000 : ℚ) : ℝ) ≤ stT250 430 := by
  have hc : ((-467787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225587006241/5000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-467787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c431 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-39039/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58439/80000) (δ := 1583/125000000) (ψ := -540941/500000) 250 242
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t431 : ((-4701356261/100000000000 : ℚ) : ℝ) ≤ stT250 431 := by
  have hc : ((-39041/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4701356261/100000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-39041/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c432 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-697411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5856437/10000000) (δ := 12539/1000000000) (ψ := -540941/500000) 250 242
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t432 : ((-167783310543/5000000000000 : ℚ) : ℝ) ≤ stT250 432 := by
  have hc : ((-697461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167783310543/5000000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-697461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c433 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-192519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275707/625000) (δ := 12539/1000000000) (ψ := -540941/500000) 250 242
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t433 : ((-9254288433/1000000000000 : ℚ) : ℝ) ≤ stT250 433 := by
  have hc : ((-192569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9254288433/1000000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-192569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c434 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((186839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1484781/5000000) (δ := 12539/1000000000) (ψ := -540941/500000) 250 242
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t434 : ((8967352221/500000000000 : ℚ) : ℝ) ≤ stT250 434 := by
  have hc : ((93407/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8967352221/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((93407/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c435 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((409121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12249/80000) (δ := 1583/125000000) (ψ := -540941/500000) 250 242
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t435 : ((24518299431/625000000000 : ℚ) : ℝ) ≤ stT250 435 := by
  have hc : ((51137/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24518299431/625000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((51137/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c436 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((999263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6/625) (δ := 1583/125000000) (ψ := -540941/500000) 250 242
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t436 : ((478536095469/10000000000000 : ℚ) : ℝ) ≤ stT250 436 := by
  have hc : ((999213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478536095469/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((999213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c437 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((215153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1335813/10000000) (δ := 12539/1000000000) (ψ := -540941/500000) 250 242
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t437 : ((51457735071/1250000000000 : ℚ) : ℝ) ≤ stT250 437 := by
  have hc : ((430281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51457735071/1250000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((430281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c438 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((224221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1382219/5000000) (δ := 12539/1000000000) (ψ := -540941/500000) 250 242
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t438 : ((13390610541/625000000000 : ℚ) : ℝ) ≤ stT250 438 := by
  have hc : ((56049/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13390610541/625000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((56049/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c439 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-10491/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16759/40000) (δ := 1583/125000000) (ψ := -540941/500000) 250 242
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t439 : ((-9784117/1953125000 : ℚ) : ℝ) ≤ stT250 439 := by
  have hc : ((-328/3125 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9784117/1953125000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-328/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c440 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-624061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5611813/10000000) (δ := 12539/1000000000) (ψ := -540941/500000) 250 242
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t440 : ((-74383421313/2500000000000 : ℚ) : ℝ) ≤ stT250 440 := by
  have hc : ((-624111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74383421313/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-624111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c441 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-189251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11249/16000) (δ := 1583/125000000) (ψ := -540941/500000) 250 242
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t441 : ((-90124384851/2000000000000 : ℚ) : ℝ) ≤ stT250 441 := by
  have hc : ((-189261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90124384851/2000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-189261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c442 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-243017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7261713/10000000) (δ := 12557/1000000000) (ψ := -540941/500000) 250 243
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t442 : ((-57798733867/1250000000000 : ℚ) : ℝ) ≤ stT250 442 := by
  have hc : ((-486059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57798733867/1250000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-486059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c443 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-139071/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233971/400000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t443 : ((-13215893863/400000000000 : ℚ) : ℝ) ≤ stT250 443 := by
  have hc : ((-139081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13215893863/400000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-139081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c444 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-3184/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177601/400000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t444 : ((-48365769627/5000000000000 : ℚ) : ℝ) ≤ stT250 444 := by
  have hc : ((-101913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48365769627/5000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-101913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c445 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((349663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3033963/10000000) (δ := 12557/1000000000) (ψ := -540941/500000) 250 243
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t445 : ((33146458917/2000000000000 : ℚ) : ℝ) ≤ stT250 445 := by
  have hc : ((349613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33146458917/2000000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((349613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c446 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((794623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65241/400000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t446 : ((376240644949/10000000000000 : ℚ) : ℝ) ≤ stT250 446 := by
  have hc : ((794573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376240644949/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((794573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c447 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((248931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9251/400000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t447 : ((235468437771/5000000000000 : ℚ) : ℝ) ≤ stT250 447 := by
  have hc : ((497837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235468437771/5000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((497837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c448 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((893299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291353/2500000) (δ := 12557/1000000000) (ψ := -540941/500000) 250 243
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t448 : ((84403991259/2000000000000 : ℚ) : ℝ) ≤ stT250 448 := by
  have hc : ((893249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84403991259/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((893249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c449 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((20813/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39983/156250) (δ := 12557/1000000000) (ψ := -540941/500000) 250 243
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t449 : ((9821314419/400000000000 : ℚ) : ℝ) ≤ stT250 449 := by
  have hc : ((20811/40000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9821314419/400000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((20811/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c450 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-559/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78987/200000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t450 : ((-423981657/1000000000000 : ℚ) : ℝ) ≤ stT250 450 := by
  have hc : ((-4497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-423981657/1000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-4497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c451 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-534481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213469/400000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t451 : ((-125850513171/5000000000000 : ℚ) : ℝ) ≤ stT250 451 := by
  have hc : ((-534531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125850513171/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-534531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c452 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-899049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268839/400000) (δ := 6323/500000000) (ψ := -540941/500000) 250 243
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t452 : ((-422901104739/10000000000000 : ℚ) : ℝ) ≤ stT250 452 := by
  have hc : ((-899099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422901104739/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-899099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c453 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-497537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7605739/10000000) (δ := 253/20000000) (ψ := -540941/500000) 250 244
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t453 : ((-116887513821/2500000000000 : ℚ) : ℝ) ≤ stT250 453 := by
  have hc : ((-248781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116887513821/2500000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-248781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c454 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-795753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3113807/5000000) (δ := 253/20000000) (ψ := -540941/500000) 250 244
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t454 : ((-93372361793/2500000000000 : ℚ) : ℝ) ≤ stT250 454 := by
  have hc : ((-795803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93372361793/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-795803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c455 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-180889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2426213/5000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t455 : ((-5300870657/312500000000 : ℚ) : ℝ) ≤ stT250 455 := by
  have hc : ((-90457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5300870657/312500000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-90457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c456 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((177727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3480301/10000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t456 : ((20801179421/2500000000000 : ℚ) : ℝ) ≤ stT250 456 := by
  have hc : ((177677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20801179421/2500000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((177677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c457 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((166027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2111239/10000000) (δ := 253/20000000) (ψ := -540941/500000) 250 244
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t457 : ((7765826281/250000000000 : ℚ) : ℝ) ≤ stT250 457 := by
  have hc : ((332029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7765826281/250000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((332029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c458 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((119489/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -372557/5000000) (δ := 253/20000000) (ψ := -540941/500000) 250 244
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t458 : ((223322340439/5000000000000 : ℚ) : ℝ) ≤ stT250 458 := by
  have hc : ((477931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223322340439/5000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((477931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c459 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((484797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309037/5000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t459 : ((1414201117/31250000000 : ℚ) : ℝ) ≤ stT250 459 := by
  have hc : ((121193/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1414201117/31250000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((121193/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c460 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((87867/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1978199/10000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t460 : ((40965250409/1250000000000 : ℚ) : ℝ) ≤ stT250 460 := by
  have hc : ((351443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40965250409/1250000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((351443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c461 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((46883/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3335449/10000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t461 : ((10915456129/1000000000000 : ℚ) : ℝ) ≤ stT250 461 := by
  have hc : ((46873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10915456129/1000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((46873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c462 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-300373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4689699/10000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t462 : ((-139769697789/10000000000000 : ℚ) : ℝ) ≤ stT250 462 := by
  have hc : ((-300423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139769697789/10000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-300423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c463 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-748391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3020537/5000000) (δ := 12553/1000000000) (ψ := -540941/500000) 250 244
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t463 : ((-17391523517/500000000000 : ℚ) : ℝ) ≤ stT250 463 := by
  have hc : ((-748441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17391523517/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-748441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c464 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-982791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7389511/10000000) (δ := 253/20000000) (ψ := -540941/500000) 250 244
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t464 : ((-456273122999/10000000000000 : ℚ) : ℝ) ≤ stT250 464 := by
  have hc : ((-982841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456273122999/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-982841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c465 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-469267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6972889/10000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t465 : ((-54407250697/1250000000000 : ℚ) : ℝ) ≤ stT250 465 := by
  have hc : ((-117323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54407250697/1250000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-117323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c466 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-629811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703783/1250000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t466 : ((-145889034681/5000000000000 : ℚ) : ℝ) ≤ stT250 466 := by
  have hc : ((-629861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145889034681/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-629861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c467 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-144897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2145257/5000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t467 : ((-13414699903/2000000000000 : ℚ) : ℝ) ≤ stT250 467 := by
  have hc : ((-144947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13414699903/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-144947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c468 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((379579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2953639/10000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t468 : ((701749121/40000000000 : ℚ) : ℝ) ≤ stT250 468 := by
  have hc : ((379529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((701749121/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((379529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c469 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((159479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1619577/10000000) (δ := 12543/1000000000) (ψ := -540941/500000) 250 245
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t469 : ((73635927033/2000000000000 : ℚ) : ℝ) ≤ stT250 469 := by
  have hc : ((159469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73635927033/2000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((159469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c470 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((496677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288389/10000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t470 : ((11454409239/250000000000 : ℚ) : ℝ) ≤ stT250 470 := by
  have hc : ((124163/125000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11454409239/250000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((124163/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c471 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((182943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519993/5000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t471 : ((3371638123/80000000000 : ℚ) : ℝ) ≤ stT250 471 := by
  have hc : ((182933/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3371638123/80000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((182933/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c472 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((292377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591387/2500000) (δ := 12543/1000000000) (ψ := -540941/500000) 250 245
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t472 : ((262823877/9765625000 : ℚ) : ℝ) ≤ stT250 472 := by
  have hc : ((9136/15625 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262823877/9765625000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((9136/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c473 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((23833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1844149/5000000) (δ := 12543/1000000000) (ψ := -540941/500000) 250 245
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t473 : ((109526659/25000000000 : ℚ) : ℝ) ≤ stT250 473 := by
  have hc : ((47641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109526659/25000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((47641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c474 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-419163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2504149/5000000) (δ := 12543/1000000000) (ψ := -540941/500000) 250 245
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t474 : ((-48137809577/2500000000000 : ℚ) : ℝ) ≤ stT250 474 := by
  have hc : ((-419213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48137809577/2500000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-419213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c475 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-409423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3162743/5000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t475 : ((-1467717537/39062500000 : ℚ) : ℝ) ≤ stT250 475 := by
  have hc : ((-51181/62500 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1467717537/39062500000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-51181/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c476 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-498167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7639861/10000000) (δ := 633/50000000) (ψ := -540941/500000) 250 245
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t476 : ((-285432879/6250000000 : ℚ) : ℝ) ≤ stT250 476 := by
  have hc : ((-31137/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285432879/6250000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-31137/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c477 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-905177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3378239/5000000) (δ := 2527/200000000) (ψ := -540941/500000) 250 246
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t477 : ((-414475381263/10000000000000 : ℚ) : ℝ) ≤ stT250 477 := by
  have hc : ((-905227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-414475381263/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-905227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c478 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-571407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272377/500000) (δ := 1571/125000000) (ψ := -540941/500000) 250 246
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t478 : ((-26137871723/1000000000000 : ℚ) : ℝ) ≤ stT250 478 := by
  have hc : ((-571457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26137871723/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-571457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c479 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-17133/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -828283/2000000) (δ := 1571/125000000) (ψ := -540941/500000) 250 246
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t479 : ((-489552651/125000000000 : ℚ) : ℝ) ≤ stT250 479 := by
  have hc : ((-17143/200000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489552651/125000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-17143/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c480 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((210991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -567583/2000000) (δ := 1571/125000000) (ψ := -540941/500000) 250 246
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t480 : ((9629226621/500000000000 : ℚ) : ℝ) ≤ stT250 480 := by
  have hc : ((105483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9629226621/500000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((105483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c481 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((204209/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -384307/2500000) (δ := 2527/200000000) (ψ := -540941/500000) 250 246
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t481 : ((4655271807/125000000000 : ℚ) : ℝ) ≤ stT250 481 := by
  have hc : ((408393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4655271807/125000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((408393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c482 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((995427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47833/2000000) (δ := 1571/125000000) (ψ := -540941/500000) 250 246
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t482 : ((453381283599/10000000000000 : ℚ) : ℝ) ≤ stT250 482 := by
  have hc : ((995377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453381283599/10000000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((995377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c483 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((228021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1056147/10000000) (δ := 2527/200000000) (ψ := -540941/500000) 250 246
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t483 : ((41498915051/1000000000000 : ℚ) : ℝ) ≤ stT250 483 := by
  have hc : ((456017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41498915051/1000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((456017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c484 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((147541/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469767/2000000) (δ := 1571/125000000) (ψ := -540941/500000) 250 246
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t484 : ((26823336813/1000000000000 : ℚ) : ℝ) ≤ stT250 484 := by
  have hc : ((295057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26823336813/1000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((295057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c485 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((14379/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 909693/2500000) (δ := 2527/200000000) (ψ := -540941/500000) 250 246
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t485 : ((6526320829/1250000000000 : ℚ) : ℝ) ≤ stT250 485 := by
  have hc : ((57491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6526320829/1250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((57491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c486 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-389107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4926147/10000000) (δ := 2527/200000000) (ψ := -540941/500000) 250 246
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t486 : ((-17652550677/1000000000000 : ℚ) : ℝ) ≤ stT250 486 := by
  have hc : ((-389157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17652550677/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-389157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c487 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-79167/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1242167/2000000) (δ := 1571/125000000) (ψ := -540941/500000) 250 246
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t487 : ((-1121134899/31250000000 : ℚ) : ℝ) ≤ stT250 487 := by
  have hc : ((-19793/25000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1121134899/31250000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-19793/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c488 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-247397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7492897/10000000) (δ := 2527/200000000) (ψ := -540941/500000) 250 246
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t488 : ((-223994170101/5000000000000 : ℚ) : ℝ) ≤ stT250 488 := by
  have hc : ((-494819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223994170101/5000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-494819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c489 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-466647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6935691/10000000) (δ := 783/62500000) (ψ := -540941/500000) 250 247
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t489 : ((-1648723009/39062500000 : ℚ) : ℝ) ≤ stT250 489 := by
  have hc : ((-29167/31250 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1648723009/39062500000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-29167/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c490 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-638659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2829439/5000000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t490 : ((-144269672793/5000000000000 : ℚ) : ℝ) ≤ stT250 490 := by
  have hc : ((-638709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144269672793/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-638709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c491 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-91017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1096157/2500000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t491 : ((-10271677087/1250000000000 : ℚ) : ℝ) ≤ stT250 491 := by
  have hc : ((-45521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10271677087/1250000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-45521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c492 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((319873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3113003/10000000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t492 : ((72093541191/5000000000000 : ℚ) : ℝ) ≤ stT250 492 := by
  have hc : ((319823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72093541191/5000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((319823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c493 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((185021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1844003/10000000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t493 : ((166647146409/5000000000000 : ℚ) : ℝ) ≤ stT250 493 := by
  have hc : ((370017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166647146409/5000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((370017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c494 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((486719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -577503/10000000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t494 : ((109486925587/2500000000000 : ℚ) : ℝ) ≤ stT250 494 := by
  have hc : ((243347/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109486925587/2500000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((243347/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c495 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((240637/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171593/2500000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t495 : ((108152531517/2500000000000 : ℚ) : ℝ) ≤ stT250 495 := by
  have hc : ((481249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108152531517/2500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((481249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c496 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((711547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1947747/10000000) (δ := 507/40000000) (ψ := -540941/500000) 250 247
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t496 : ((319471402461/10000000000000 : ℚ) : ℝ) ≤ stT250 496 := by
  have hc : ((711497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319471402461/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((711497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c497 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((284201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3206559/10000000) (δ := 783/62500000) (ψ := -540941/500000) 250 247
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t497 : ((127459056711/10000000000000 : ℚ) : ℝ) ≤ stT250 497 := by
  have hc : ((284151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127459056711/10000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((284151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c498 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-21269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4462809/10000000) (δ := 783/62500000) (ψ := -540941/500000) 250 247
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t498 : ((-4766556707/500000000000 : ℚ) : ℝ) ≤ stT250 498 := by
  have hc : ((-10637/50000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4766556707/500000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-10637/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c499 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-328121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5716559/10000000) (δ := 783/62500000) (ψ := -540941/500000) 250 247
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t499 : ((-36724623663/1250000000000 : ℚ) : ℝ) ≤ stT250 499 := by
  have hc : ((-164073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36724623663/1250000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-164073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_c500 :
    |Real.cos (((250 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((-937831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6967809/10000000) (δ := 783/62500000) (ψ := -540941/500000) 250 247
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st250_t500 : ((-209716756767/5000000000000 : ℚ) : ℝ) ≤ stT250 500 := by
  have hc : ((-937881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((250 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st250_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209716756767/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-937881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st250_p1 : ((234809/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT250 (i+1) := by
  rw [Finset.sum_range_one]
  exact st250_t1

theorem st250_p2 : ((4768495802209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT250 (i+1))
      = (∑ i ∈ Finset.range 1, stT250 (i+1)) + stT250 2 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 1
    simpa using h
  have hprev := st250_p1
  have hstep := st250_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p3 : ((9088870857331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT250 (i+1))
      = (∑ i ∈ Finset.range 2, stT250 (i+1)) + stT250 3 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 2
    simpa using h
  have hprev := st250_p2
  have hstep := st250_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p4 : ((6650000369557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT250 (i+1))
      = (∑ i ∈ Finset.range 3, stT250 (i+1)) + stT250 4 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 3
    simpa using h
  have hprev := st250_p3
  have hstep := st250_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p5 : ((1942608914013/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT250 (i+1))
      = (∑ i ∈ Finset.range 4, stT250 (i+1)) + stT250 5 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 4
    simpa using h
  have hprev := st250_p4
  have hstep := st250_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p6 : ((151662806283/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT250 (i+1))
      = (∑ i ∈ Finset.range 5, stT250 (i+1)) + stT250 6 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 5
    simpa using h
  have hprev := st250_p5
  have hstep := st250_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p7 : ((27958049149/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT250 (i+1))
      = (∑ i ∈ Finset.range 6, stT250 (i+1)) + stT250 7 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 6
    simpa using h
  have hprev := st250_p6
  have hstep := st250_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p8 : ((3690302060431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT250 (i+1))
      = (∑ i ∈ Finset.range 7, stT250 (i+1)) + stT250 8 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 7
    simpa using h
  have hprev := st250_p7
  have hstep := st250_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p9 : ((956648180367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT250 (i+1))
      = (∑ i ∈ Finset.range 8, stT250 (i+1)) + stT250 9 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 8
    simpa using h
  have hprev := st250_p8
  have hstep := st250_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p10 : ((1726257858411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT250 (i+1))
      = (∑ i ∈ Finset.range 9, stT250 (i+1)) + stT250 10 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 9
    simpa using h
  have hprev := st250_p9
  have hstep := st250_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p11 : ((-903108486657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT250 (i+1))
      = (∑ i ∈ Finset.range 10, stT250 (i+1)) + stT250 11 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 10
    simpa using h
  have hprev := st250_p10
  have hstep := st250_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p12 : ((117277327591/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT250 (i+1))
      = (∑ i ∈ Finset.range 11, stT250 (i+1)) + stT250 12 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 11
    simpa using h
  have hprev := st250_p11
  have hstep := st250_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p13 : ((563411777239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT250 (i+1))
      = (∑ i ∈ Finset.range 12, stT250 (i+1)) + stT250 13 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 12
    simpa using h
  have hprev := st250_p12
  have hstep := st250_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p14 : ((171884987427/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT250 (i+1))
      = (∑ i ∈ Finset.range 13, stT250 (i+1)) + stT250 14 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 13
    simpa using h
  have hprev := st250_p13
  have hstep := st250_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p15 : ((1429067002677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT250 (i+1))
      = (∑ i ∈ Finset.range 14, stT250 (i+1)) + stT250 15 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 14
    simpa using h
  have hprev := st250_p14
  have hstep := st250_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p16 : ((805271753159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT250 (i+1))
      = (∑ i ∈ Finset.range 15, stT250 (i+1)) + stT250 16 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 15
    simpa using h
  have hprev := st250_p15
  have hstep := st250_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p17 : ((650290493587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT250 (i+1))
      = (∑ i ∈ Finset.range 16, stT250 (i+1)) + stT250 17 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 16
    simpa using h
  have hprev := st250_p16
  have hstep := st250_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p18 : ((1563357120377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT250 (i+1))
      = (∑ i ∈ Finset.range 17, stT250 (i+1)) + stT250 18 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 17
    simpa using h
  have hprev := st250_p17
  have hstep := st250_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p19 : ((258869289491/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT250 (i+1))
      = (∑ i ∈ Finset.range 18, stT250 (i+1)) + stT250 19 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 18
    simpa using h
  have hprev := st250_p18
  have hstep := st250_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p20 : ((457640466437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT250 (i+1))
      = (∑ i ∈ Finset.range 19, stT250 (i+1)) + stT250 20 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 19
    simpa using h
  have hprev := st250_p19
  have hstep := st250_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p21 : ((1429575563603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT250 (i+1))
      = (∑ i ∈ Finset.range 20, stT250 (i+1)) + stT250 21 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 20
    simpa using h
  have hprev := st250_p20
  have hstep := st250_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p22 : ((1995853678859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT250 (i+1))
      = (∑ i ∈ Finset.range 21, stT250 (i+1)) + stT250 22 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 21
    simpa using h
  have hprev := st250_p21
  have hstep := st250_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p23 : ((2937859183739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT250 (i+1))
      = (∑ i ∈ Finset.range 22, stT250 (i+1)) + stT250 23 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 22
    simpa using h
  have hprev := st250_p22
  have hstep := st250_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p24 : ((2206802650133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT250 (i+1))
      = (∑ i ∈ Finset.range 23, stT250 (i+1)) + stT250 24 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 23
    simpa using h
  have hprev := st250_p23
  have hstep := st250_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p25 : ((2224422650133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT250 (i+1))
      = (∑ i ∈ Finset.range 24, stT250 (i+1)) + stT250 25 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 24
    simpa using h
  have hprev := st250_p24
  have hstep := st250_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p26 : ((64307677911/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT250 (i+1))
      = (∑ i ∈ Finset.range 25, stT250 (i+1)) + stT250 26 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 25
    simpa using h
  have hprev := st250_p25
  have hstep := st250_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p27 : ((2221584129699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT250 (i+1))
      = (∑ i ∈ Finset.range 26, stT250 (i+1)) + stT250 27 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 26
    simpa using h
  have hprev := st250_p26
  have hstep := st250_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p28 : ((1129741782499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT250 (i+1))
      = (∑ i ∈ Finset.range 27, stT250 (i+1)) + stT250 28 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 27
    simpa using h
  have hprev := st250_p27
  have hstep := st250_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p29 : ((558537438493/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT250 (i+1))
      = (∑ i ∈ Finset.range 28, stT250 (i+1)) + stT250 29 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 28
    simpa using h
  have hprev := st250_p28
  have hstep := st250_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p30 : ((1879812540981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT250 (i+1))
      = (∑ i ∈ Finset.range 29, stT250 (i+1)) + stT250 30 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 29
    simpa using h
  have hprev := st250_p29
  have hstep := st250_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p31 : ((1095157989837/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT250 (i+1))
      = (∑ i ∈ Finset.range 30, stT250 (i+1)) + stT250 31 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 30
    simpa using h
  have hprev := st250_p30
  have hstep := st250_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p32 : ((2991355277733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT250 (i+1))
      = (∑ i ∈ Finset.range 31, stT250 (i+1)) + stT250 32 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 31
    simpa using h
  have hprev := st250_p31
  have hstep := st250_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p33 : ((2754780201879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT250 (i+1))
      = (∑ i ∈ Finset.range 32, stT250 (i+1)) + stT250 33 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 32
    simpa using h
  have hprev := st250_p32
  have hstep := st250_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p34 : ((951479759037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT250 (i+1))
      = (∑ i ∈ Finset.range 33, stT250 (i+1)) + stT250 34 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 33
    simpa using h
  have hprev := st250_p33
  have hstep := st250_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p35 : ((335992737789/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT250 (i+1))
      = (∑ i ∈ Finset.range 34, stT250 (i+1)) + stT250 35 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 34
    simpa using h
  have hprev := st250_p34
  have hstep := st250_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p36 : ((137468593887/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT250 (i+1))
      = (∑ i ∈ Finset.range 35, stT250 (i+1)) + stT250 36 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 35
    simpa using h
  have hprev := st250_p35
  have hstep := st250_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p37 : ((1841136581829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT250 (i+1))
      = (∑ i ∈ Finset.range 36, stT250 (i+1)) + stT250 37 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 36
    simpa using h
  have hprev := st250_p36
  have hstep := st250_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p38 : ((629504790537/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT250 (i+1))
      = (∑ i ∈ Finset.range 37, stT250 (i+1)) + stT250 38 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 37
    simpa using h
  have hprev := st250_p37
  have hstep := st250_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p39 : ((1631818222213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT250 (i+1))
      = (∑ i ∈ Finset.range 38, stT250 (i+1)) + stT250 39 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 38
    simpa using h
  have hprev := st250_p38
  have hstep := st250_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p40 : ((1003100434211/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT250 (i+1))
      = (∑ i ∈ Finset.range 39, stT250 (i+1)) + stT250 40 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 39
    simpa using h
  have hprev := st250_p39
  have hstep := st250_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p41 : ((4720004468963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT250 (i+1))
      = (∑ i ∈ Finset.range 40, stT250 (i+1)) + stT250 41 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 40
    simpa using h
  have hprev := st250_p40
  have hstep := st250_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p42 : ((10624751218359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT250 (i+1))
      = (∑ i ∈ Finset.range 41, stT250 (i+1)) + stT250 42 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 41
    simpa using h
  have hprev := st250_p41
  have hstep := st250_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p43 : ((707625017819/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT250 (i+1))
      = (∑ i ∈ Finset.range 42, stT250 (i+1)) + stT250 43 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 42
    simpa using h
  have hprev := st250_p42
  have hstep := st250_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p44 : ((11230185541133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT250 (i+1))
      = (∑ i ∈ Finset.range 43, stT250 (i+1)) + stT250 44 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 43
    simpa using h
  have hprev := st250_p43
  have hstep := st250_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p45 : ((10240589796341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT250 (i+1))
      = (∑ i ∈ Finset.range 44, stT250 (i+1)) + stT250 45 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 44
    simpa using h
  have hprev := st250_p44
  have hstep := st250_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p46 : ((8768444826401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT250 (i+1))
      = (∑ i ∈ Finset.range 45, stT250 (i+1)) + stT250 46 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 45
    simpa using h
  have hprev := st250_p45
  have hstep := st250_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p47 : ((7805852518401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT250 (i+1))
      = (∑ i ∈ Finset.range 46, stT250 (i+1)) + stT250 47 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 46
    simpa using h
  have hprev := st250_p46
  have hstep := st250_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p48 : ((4115603957013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT250 (i+1))
      = (∑ i ∈ Finset.range 47, stT250 (i+1)) + stT250 48 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 47
    simpa using h
  have hprev := st250_p47
  have hstep := st250_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p49 : ((9645080347007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT250 (i+1))
      = (∑ i ∈ Finset.range 48, stT250 (i+1)) + stT250 49 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 48
    simpa using h
  have hprev := st250_p48
  have hstep := st250_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p50 : ((10299985416751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT250 (i+1))
      = (∑ i ∈ Finset.range 49, stT250 (i+1)) + stT250 50 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 49
    simpa using h
  have hprev := st250_p49
  have hstep := st250_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p51 : ((9246985306999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT250 (i+1))
      = (∑ i ∈ Finset.range 50, stT250 (i+1)) + stT250 51 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 50
    simpa using h
  have hprev := st250_p50
  have hstep := st250_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p52 : ((8194233285349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT250 (i+1))
      = (∑ i ∈ Finset.range 51, stT250 (i+1)) + stT250 52 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 51
    simpa using h
  have hprev := st250_p51
  have hstep := st250_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p53 : ((1129435319743/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT250 (i+1))
      = (∑ i ∈ Finset.range 52, stT250 (i+1)) + stT250 53 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 52
    simpa using h
  have hprev := st250_p52
  have hstep := st250_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p54 : ((2015497096519/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT250 (i+1))
      = (∑ i ∈ Finset.range 53, stT250 (i+1)) + stT250 54 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 53
    simpa using h
  have hprev := st250_p53
  have hstep := st250_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p55 : ((1817631801799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT250 (i+1))
      = (∑ i ∈ Finset.range 54, stT250 (i+1)) + stT250 55 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 54
    simpa using h
  have hprev := st250_p54
  have hstep := st250_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p56 : ((4200897826753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT250 (i+1))
      = (∑ i ∈ Finset.range 55, stT250 (i+1)) + stT250 56 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 55
    simpa using h
  have hprev := st250_p55
  have hstep := st250_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p57 : ((4842236883419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT250 (i+1))
      = (∑ i ∈ Finset.range 56, stT250 (i+1)) + stT250 57 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 56
    simpa using h
  have hprev := st250_p56
  have hstep := st250_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p58 : ((9536897078423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT250 (i+1))
      = (∑ i ∈ Finset.range 57, stT250 (i+1)) + stT250 58 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 57
    simpa using h
  have hprev := st250_p57
  have hstep := st250_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p59 : ((8427870364913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT250 (i+1))
      = (∑ i ∈ Finset.range 58, stT250 (i+1)) + stT250 59 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 58
    simpa using h
  have hprev := st250_p58
  have hstep := st250_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p60 : ((382210422731/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT250 (i+1))
      = (∑ i ∈ Finset.range 59, stT250 (i+1)) + stT250 60 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 59
    simpa using h
  have hprev := st250_p59
  have hstep := st250_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p61 : ((2366012090271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT250 (i+1))
      = (∑ i ∈ Finset.range 60, stT250 (i+1)) + stT250 61 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 60
    simpa using h
  have hprev := st250_p60
  have hstep := st250_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p62 : ((4253973202707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT250 (i+1))
      = (∑ i ∈ Finset.range 61, stT250 (i+1)) + stT250 62 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 61
    simpa using h
  have hprev := st250_p61
  have hstep := st250_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p63 : ((9755438995541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT250 (i+1))
      = (∑ i ∈ Finset.range 62, stT250 (i+1)) + stT250 63 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 62
    simpa using h
  have hprev := st250_p62
  have hstep := st250_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p64 : ((1126697769007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT250 (i+1))
      = (∑ i ∈ Finset.range 63, stT250 (i+1)) + stT250 64 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 63
    simpa using h
  have hprev := st250_p63
  have hstep := st250_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p65 : ((2222689172839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT250 (i+1))
      = (∑ i ∈ Finset.range 64, stT250 (i+1)) + stT250 65 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 64
    simpa using h
  have hprev := st250_p64
  have hstep := st250_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p66 : ((975147453677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT250 (i+1))
      = (∑ i ∈ Finset.range 65, stT250 (i+1)) + stT250 66 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 65
    simpa using h
  have hprev := st250_p65
  have hstep := st250_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p67 : ((427456437109/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT250 (i+1))
      = (∑ i ∈ Finset.range 66, stT250 (i+1)) + stT250 67 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 66
    simpa using h
  have hprev := st250_p66
  have hstep := st250_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p68 : ((96735722909/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT250 (i+1))
      = (∑ i ∈ Finset.range 67, stT250 (i+1)) + stT250 68 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 67
    simpa using h
  have hprev := st250_p67
  have hstep := st250_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p69 : ((4458734692103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT250 (i+1))
      = (∑ i ∈ Finset.range 68, stT250 (i+1)) + stT250 69 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 68
    simpa using h
  have hprev := st250_p68
  have hstep := st250_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p70 : ((4591115157313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT250 (i+1))
      = (∑ i ∈ Finset.range 69, stT250 (i+1)) + stT250 70 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 69
    simpa using h
  have hprev := st250_p69
  have hstep := st250_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p71 : ((4697984786363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT250 (i+1))
      = (∑ i ∈ Finset.range 70, stT250 (i+1)) + stT250 71 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 70
    simpa using h
  have hprev := st250_p70
  have hstep := st250_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p72 : ((4396960412483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT250 (i+1))
      = (∑ i ∈ Finset.range 71, stT250 (i+1)) + stT250 72 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 71
    simpa using h
  have hprev := st250_p71
  have hstep := st250_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p73 : ((4833812807/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT250 (i+1))
      = (∑ i ∈ Finset.range 72, stT250 (i+1)) + stT250 73 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 72
    simpa using h
  have hprev := st250_p72
  have hstep := st250_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p74 : ((8630160228103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT250 (i+1))
      = (∑ i ∈ Finset.range 73, stT250 (i+1)) + stT250 74 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 73
    simpa using h
  have hprev := st250_p73
  have hstep := st250_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p75 : ((9747767800003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT250 (i+1))
      = (∑ i ∈ Finset.range 74, stT250 (i+1)) + stT250 75 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 74
    simpa using h
  have hprev := st250_p74
  have hstep := st250_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p76 : ((4302350067633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT250 (i+1))
      = (∑ i ∈ Finset.range 75, stT250 (i+1)) + stT250 76 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 75
    simpa using h
  have hprev := st250_p75
  have hstep := st250_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p77 : ((4871616953283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT250 (i+1))
      = (∑ i ∈ Finset.range 76, stT250 (i+1)) + stT250 77 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 76
    simpa using h
  have hprev := st250_p76
  have hstep := st250_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p78 : ((430996913397/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT250 (i+1))
      = (∑ i ∈ Finset.range 77, stT250 (i+1)) + stT250 78 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 77
    simpa using h
  have hprev := st250_p77
  have hstep := st250_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p79 : ((4864413132657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT250 (i+1))
      = (∑ i ∈ Finset.range 78, stT250 (i+1)) + stT250 79 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 78
    simpa using h
  have hprev := st250_p78
  have hstep := st250_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p80 : ((1078421169429/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT250 (i+1))
      = (∑ i ∈ Finset.range 79, stT250 (i+1)) + stT250 80 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 79
    simpa using h
  have hprev := st250_p79
  have hstep := st250_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p81 : ((608003355613/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT250 (i+1))
      = (∑ i ∈ Finset.range 80, stT250 (i+1)) + stT250 81 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 80
    simpa using h
  have hprev := st250_p80
  have hstep := st250_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p82 : ((2156462561579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT250 (i+1))
      = (∑ i ∈ Finset.range 81, stT250 (i+1)) + stT250 82 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 81
    simpa using h
  have hprev := st250_p81
  have hstep := st250_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p83 : ((4861071622149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT250 (i+1))
      = (∑ i ∈ Finset.range 82, stT250 (i+1)) + stT250 83 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 82
    simpa using h
  have hprev := st250_p82
  have hstep := st250_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p84 : ((2162978994047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT250 (i+1))
      = (∑ i ∈ Finset.range 83, stT250 (i+1)) + stT250 84 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 83
    simpa using h
  have hprev := st250_p83
  have hstep := st250_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p85 : ((482974955649/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT250 (i+1))
      = (∑ i ∈ Finset.range 84, stT250 (i+1)) + stT250 85 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 84
    simpa using h
  have hprev := st250_p84
  have hstep := st250_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p86 : ((2191864147073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT250 (i+1))
      = (∑ i ∈ Finset.range 85, stT250 (i+1)) + stT250 86 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 85
    simpa using h
  have hprev := st250_p85
  have hstep := st250_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p87 : ((2369133845853/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT250 (i+1))
      = (∑ i ∈ Finset.range 86, stT250 (i+1)) + stT250 87 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 86
    simpa using h
  have hprev := st250_p86
  have hstep := st250_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p88 : ((225601403189/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT250 (i+1))
      = (∑ i ∈ Finset.range 87, stT250 (i+1)) + stT250 88 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 87
    simpa using h
  have hprev := st250_p87
  have hstep := st250_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p89 : ((9152577583819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT250 (i+1))
      = (∑ i ∈ Finset.range 88, stT250 (i+1)) + stT250 89 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 88
    simpa using h
  have hprev := st250_p88
  have hstep := st250_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p90 : ((9389417298931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT250 (i+1))
      = (∑ i ∈ Finset.range 89, stT250 (i+1)) + stT250 90 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 89
    simpa using h
  have hprev := st250_p89
  have hstep := st250_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p91 : ((8792448343411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT250 (i+1))
      = (∑ i ∈ Finset.range 90, stT250 (i+1)) + stT250 91 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 90
    simpa using h
  have hprev := st250_p90
  have hstep := st250_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p92 : ((9678113257411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT250 (i+1))
      = (∑ i ∈ Finset.range 91, stT250 (i+1)) + stT250 92 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 91
    simpa using h
  have hprev := st250_p91
  have hstep := st250_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p93 : ((8648174163787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT250 (i+1))
      = (∑ i ∈ Finset.range 92, stT250 (i+1)) + stT250 93 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 92
    simpa using h
  have hprev := st250_p92
  have hstep := st250_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p94 : ((2404166784289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT250 (i+1))
      = (∑ i ∈ Finset.range 93, stT250 (i+1)) + stT250 94 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 93
    simpa using h
  have hprev := st250_p93
  have hstep := st250_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p95 : ((8937207414511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT250 (i+1))
      = (∑ i ∈ Finset.range 94, stT250 (i+1)) + stT250 95 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 94
    simpa using h
  have hprev := st250_p94
  have hstep := st250_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p96 : ((9139911732091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT250 (i+1))
      = (∑ i ∈ Finset.range 95, stT250 (i+1)) + stT250 96 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 95
    simpa using h
  have hprev := st250_p95
  have hstep := st250_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p97 : ((9488882090907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT250 (i+1))
      = (∑ i ∈ Finset.range 96, stT250 (i+1)) + stT250 97 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 96
    simpa using h
  have hprev := st250_p96
  have hstep := st250_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p98 : ((2170014408643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT250 (i+1))
      = (∑ i ∈ Finset.range 97, stT250 (i+1)) + stT250 98 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 97
    simpa using h
  have hprev := st250_p97
  have hstep := st250_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p99 : ((2421070641169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT250 (i+1))
      = (∑ i ∈ Finset.range 98, stT250 (i+1)) + stT250 99 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 98
    simpa using h
  have hprev := st250_p98
  have hstep := st250_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p100 : ((2213334641169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT250 (i+1))
      = (∑ i ∈ Finset.range 99, stT250 (i+1)) + stT250 100 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 99
    simpa using h
  have hprev := st250_p99
  have hstep := st250_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p101 : ((1834526600499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT250 (i+1))
      = (∑ i ∈ Finset.range 100, stT250 (i+1)) + stT250 101 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 100
    simpa using h
  have hprev := st250_p100
  have hstep := st250_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p102 : ((4756887639717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT250 (i+1))
      = (∑ i ∈ Finset.range 101, stT250 (i+1)) + stT250 102 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 101
    simpa using h
  have hprev := st250_p101
  have hstep := st250_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p103 : ((541055990889/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT250 (i+1))
      = (∑ i ∈ Finset.range 102, stT250 (i+1)) + stT250 103 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 102
    simpa using h
  have hprev := st250_p102
  have hstep := st250_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p104 : ((1201993525113/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT250 (i+1))
      = (∑ i ∈ Finset.range 103, stT250 (i+1)) + stT250 104 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 103
    simpa using h
  have hprev := st250_p103
  have hstep := st250_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p105 : ((9055325281137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT250 (i+1))
      = (∑ i ∈ Finset.range 104, stT250 (i+1)) + stT250 105 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 104
    simpa using h
  have hprev := st250_p104
  have hstep := st250_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p106 : ((8900508120453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT250 (i+1))
      = (∑ i ∈ Finset.range 105, stT250 (i+1)) + stT250 106 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 105
    simpa using h
  have hprev := st250_p105
  have hstep := st250_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p107 : ((9689155881477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT250 (i+1))
      = (∑ i ∈ Finset.range 106, stT250 (i+1)) + stT250 107 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 106
    simpa using h
  have hprev := st250_p106
  have hstep := st250_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p108 : ((1749183407347/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT250 (i+1))
      = (∑ i ∈ Finset.range 107, stT250 (i+1)) + stT250 108 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 107
    simpa using h
  have hprev := st250_p107
  have hstep := st250_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p109 : ((1846674768931/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT250 (i+1))
      = (∑ i ∈ Finset.range 108, stT250 (i+1)) + stT250 109 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 108
    simpa using h
  have hprev := st250_p108
  have hstep := st250_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p110 : ((1907460831817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT250 (i+1))
      = (∑ i ∈ Finset.range 109, stT250 (i+1)) + stT250 110 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 109
    simpa using h
  have hprev := st250_p109
  have hstep := st250_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p111 : ((8651373370097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT250 (i+1))
      = (∑ i ∈ Finset.range 110, stT250 (i+1)) + stT250 111 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 110
    simpa using h
  have hprev := st250_p110
  have hstep := st250_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p112 : ((2366382132707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT250 (i+1))
      = (∑ i ∈ Finset.range 111, stT250 (i+1)) + stT250 112 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 111
    simpa using h
  have hprev := st250_p111
  have hstep := st250_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p113 : ((935360342769/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT250 (i+1))
      = (∑ i ∈ Finset.range 112, stT250 (i+1)) + stT250 113 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 112
    simpa using h
  have hprev := st250_p112
  have hstep := st250_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p114 : ((1083618360759/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT250 (i+1))
      = (∑ i ∈ Finset.range 113, stT250 (i+1)) + stT250 114 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 113
    simpa using h
  have hprev := st250_p113
  have hstep := st250_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p115 : ((598842348931/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT250 (i+1))
      = (∑ i ∈ Finset.range 114, stT250 (i+1)) + stT250 115 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 114
    simpa using h
  have hprev := st250_p114
  have hstep := st250_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p116 : ((2307839083503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT250 (i+1))
      = (∑ i ∈ Finset.range 115, stT250 (i+1)) + stT250 116 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 115
    simpa using h
  have hprev := st250_p115
  have hstep := st250_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p117 : ((217560493197/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT250 (i+1))
      = (∑ i ∈ Finset.range 116, stT250 (i+1)) + stT250 117 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 116
    simpa using h
  have hprev := st250_p116
  have hstep := st250_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p118 : ((481084785927/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT250 (i+1))
      = (∑ i ∈ Finset.range 117, stT250 (i+1)) + stT250 118 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 117
    simpa using h
  have hprev := st250_p117
  have hstep := st250_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p119 : ((9192866676437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT250 (i+1))
      = (∑ i ∈ Finset.range 118, stT250 (i+1)) + stT250 119 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 118
    simpa using h
  have hprev := st250_p118
  have hstep := st250_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p120 : ((8705769665289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT250 (i+1))
      = (∑ i ∈ Finset.range 119, stT250 (i+1)) + stT250 120 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 119
    simpa using h
  have hprev := st250_p119
  have hstep := st250_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p121 : ((9613238757819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT250 (i+1))
      = (∑ i ∈ Finset.range 120, stT250 (i+1)) + stT250 121 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 120
    simpa using h
  have hprev := st250_p120
  have hstep := st250_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p122 : ((9237459960981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT250 (i+1))
      = (∑ i ∈ Finset.range 121, stT250 (i+1)) + stT250 122 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 121
    simpa using h
  have hprev := st250_p121
  have hstep := st250_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p123 : ((8675504051851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT250 (i+1))
      = (∑ i ∈ Finset.range 122, stT250 (i+1)) + stT250 123 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 122
    simpa using h
  have hprev := st250_p122
  have hstep := st250_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p124 : ((9551975631799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT250 (i+1))
      = (∑ i ∈ Finset.range 123, stT250 (i+1)) + stT250 124 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 123
    simpa using h
  have hprev := st250_p123
  have hstep := st250_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p125 : ((1871707000991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT250 (i+1))
      = (∑ i ∈ Finset.range 124, stT250 (i+1)) + stT250 125 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 124
    simpa using h
  have hprev := st250_p124
  have hstep := st250_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p126 : ((432174983429/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT250 (i+1))
      = (∑ i ∈ Finset.range 125, stT250 (i+1)) + stT250 126 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 125
    simpa using h
  have hprev := st250_p125
  have hstep := st250_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p127 : ((2352701762513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT250 (i+1))
      = (∑ i ∈ Finset.range 126, stT250 (i+1)) + stT250 127 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 126
    simpa using h
  have hprev := st250_p126
  have hstep := st250_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p128 : ((953070224347/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT250 (i+1))
      = (∑ i ∈ Finset.range 127, stT250 (i+1)) + stT250 128 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 127
    simpa using h
  have hprev := st250_p127
  have hstep := st250_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p129 : ((8675158321809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT250 (i+1))
      = (∑ i ∈ Finset.range 128, stT250 (i+1)) + stT250 129 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 128
    simpa using h
  have hprev := st250_p128
  have hstep := st250_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p130 : ((9169137559743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT250 (i+1))
      = (∑ i ∈ Finset.range 129, stT250 (i+1)) + stT250 130 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 129
    simpa using h
  have hprev := st250_p129
  have hstep := st250_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p131 : ((9682083935919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT250 (i+1))
      = (∑ i ∈ Finset.range 130, stT250 (i+1)) + stT250 131 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 130
    simpa using h
  have hprev := st250_p130
  have hstep := st250_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p132 : ((8849802307117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT250 (i+1))
      = (∑ i ∈ Finset.range 131, stT250 (i+1)) + stT250 132 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 131
    simpa using h
  have hprev := st250_p131
  have hstep := st250_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p133 : ((8866086614137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT250 (i+1))
      = (∑ i ∈ Finset.range 132, stT250 (i+1)) + stT250 133 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 132
    simpa using h
  have hprev := st250_p132
  have hstep := st250_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p134 : ((77486943797/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT250 (i+1))
      = (∑ i ∈ Finset.range 133, stT250 (i+1)) + stT250 134 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 133
    simpa using h
  have hprev := st250_p133
  have hstep := st250_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p135 : ((4596870005281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT250 (i+1))
      = (∑ i ∈ Finset.range 134, stT250 (i+1)) + stT250 135 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 134
    simpa using h
  have hprev := st250_p134
  have hstep := st250_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p136 : ((1729848277597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT250 (i+1))
      = (∑ i ∈ Finset.range 135, stT250 (i+1)) + stT250 136 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 135
    simpa using h
  have hprev := st250_p135
  have hstep := st250_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p137 : ((2356693438047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT250 (i+1))
      = (∑ i ∈ Finset.range 136, stT250 (i+1)) + stT250 137 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 136
    simpa using h
  have hprev := st250_p136
  have hstep := st250_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p138 : ((2394745432503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT250 (i+1))
      = (∑ i ∈ Finset.range 137, stT250 (i+1)) + stT250 138 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 137
    simpa using h
  have hprev := st250_p137
  have hstep := st250_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p139 : ((436600366833/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT250 (i+1))
      = (∑ i ∈ Finset.range 138, stT250 (i+1)) + stT250 139 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 138
    simpa using h
  have hprev := st250_p138
  have hstep := st250_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p140 : ((2240525550867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT250 (i+1))
      = (∑ i ∈ Finset.range 139, stT250 (i+1)) + stT250 140 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 139
    simpa using h
  have hprev := st250_p139
  have hstep := st250_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p141 : ((9707349414351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT250 (i+1))
      = (∑ i ∈ Finset.range 140, stT250 (i+1)) + stT250 141 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 140
    simpa using h
  have hprev := st250_p140
  have hstep := st250_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p142 : ((9179412465513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT250 (i+1))
      = (∑ i ∈ Finset.range 141, stT250 (i+1)) + stT250 142 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 141
    simpa using h
  have hprev := st250_p141
  have hstep := st250_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p143 : ((8636279326957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT250 (i+1))
      = (∑ i ∈ Finset.range 142, stT250 (i+1)) + stT250 143 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 142
    simpa using h
  have hprev := st250_p142
  have hstep := st250_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p144 : ((4676458270151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT250 (i+1))
      = (∑ i ∈ Finset.range 143, stT250 (i+1)) + stT250 144 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 143
    simpa using h
  have hprev := st250_p143
  have hstep := st250_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p145 : ((2414487442147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT250 (i+1))
      = (∑ i ∈ Finset.range 144, stT250 (i+1)) + stT250 145 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 144
    simpa using h
  have hprev := st250_p144
  have hstep := st250_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p146 : ((885185904177/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT250 (i+1))
      = (∑ i ∈ Finset.range 145, stT250 (i+1)) + stT250 146 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 145
    simpa using h
  have hprev := st250_p145
  have hstep := st250_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p147 : ((4387586822829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT250 (i+1))
      = (∑ i ∈ Finset.range 146, stT250 (i+1)) + stT250 147 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 146
    simpa using h
  have hprev := st250_p146
  have hstep := st250_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p148 : ((1199591190357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT250 (i+1))
      = (∑ i ∈ Finset.range 147, stT250 (i+1)) + stT250 148 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 147
    simpa using h
  have hprev := st250_p147
  have hstep := st250_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p149 : ((1184911372149/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT250 (i+1))
      = (∑ i ∈ Finset.range 148, stT250 (i+1)) + stT250 149 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 148
    simpa using h
  have hprev := st250_p148
  have hstep := st250_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p150 : ((8687180293091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT250 (i+1))
      = (∑ i ∈ Finset.range 149, stT250 (i+1)) + stT250 150 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 149
    simpa using h
  have hprev := st250_p149
  have hstep := st250_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p151 : ((8955133012699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT250 (i+1))
      = (∑ i ∈ Finset.range 150, stT250 (i+1)) + stT250 151 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 150
    simpa using h
  have hprev := st250_p150
  have hstep := st250_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p152 : ((484868161979/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT250 (i+1))
      = (∑ i ∈ Finset.range 151, stT250 (i+1)) + stT250 152 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 151
    simpa using h
  have hprev := st250_p151
  have hstep := st250_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p153 : ((9321480293307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT250 (i+1))
      = (∑ i ∈ Finset.range 152, stT250 (i+1)) + stT250 153 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 152
    simpa using h
  have hprev := st250_p152
  have hstep := st250_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p154 : ((4315427665959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT250 (i+1))
      = (∑ i ∈ Finset.range 153, stT250 (i+1)) + stT250 154 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 153
    simpa using h
  have hprev := st250_p153
  have hstep := st250_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p155 : ((1134604933599/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT250 (i+1))
      = (∑ i ∈ Finset.range 154, stT250 (i+1)) + stT250 155 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 154
    simpa using h
  have hprev := st250_p154
  have hstep := st250_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p156 : ((1215723176319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT250 (i+1))
      = (∑ i ∈ Finset.range 155, stT250 (i+1)) + stT250 156 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 155
    simpa using h
  have hprev := st250_p155
  have hstep := st250_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p157 : ((9241293129723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT250 (i+1))
      = (∑ i ∈ Finset.range 156, stT250 (i+1)) + stT250 157 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 156
    simpa using h
  have hprev := st250_p156
  have hstep := st250_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p158 : ((8617087980669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT250 (i+1))
      = (∑ i ∈ Finset.range 157, stT250 (i+1)) + stT250 158 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 157
    simpa using h
  have hprev := st250_p157
  have hstep := st250_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p159 : ((9112814644157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT250 (i+1))
      = (∑ i ∈ Finset.range 158, stT250 (i+1)) + stT250 159 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 158
    simpa using h
  have hprev := st250_p158
  have hstep := st250_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p160 : ((2432875125971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT250 (i+1))
      = (∑ i ∈ Finset.range 159, stT250 (i+1)) + stT250 160 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 159
    simpa using h
  have hprev := st250_p159
  have hstep := st250_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p161 : ((1156130127099/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT250 (i+1))
      = (∑ i ∈ Finset.range 160, stT250 (i+1)) + stT250 161 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 160
    simpa using h
  have hprev := st250_p160
  have hstep := st250_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p162 : ((8616917553117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT250 (i+1))
      = (∑ i ∈ Finset.range 161, stT250 (i+1)) + stT250 162 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 161
    simpa using h
  have hprev := st250_p161
  have hstep := st250_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p163 : ((9061479480657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT250 (i+1))
      = (∑ i ∈ Finset.range 162, stT250 (i+1)) + stT250 163 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 162
    simpa using h
  have hprev := st250_p162
  have hstep := st250_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p164 : ((1944450933493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT250 (i+1))
      = (∑ i ∈ Finset.range 163, stT250 (i+1)) + stT250 164 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 163
    simpa using h
  have hprev := st250_p163
  have hstep := st250_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p165 : ((9341606024417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT250 (i+1))
      = (∑ i ∈ Finset.range 164, stT250 (i+1)) + stT250 165 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 164
    simpa using h
  have hprev := st250_p164
  have hstep := st250_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p166 : ((1728578011477/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT250 (i+1))
      = (∑ i ∈ Finset.range 165, stT250 (i+1)) + stT250 166 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 165
    simpa using h
  have hprev := st250_p165
  have hstep := st250_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p167 : ((1116354956923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT250 (i+1))
      = (∑ i ∈ Finset.range 166, stT250 (i+1)) + stT250 167 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 166
    simpa using h
  have hprev := st250_p166
  have hstep := st250_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p168 : ((48335780047/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT250 (i+1))
      = (∑ i ∈ Finset.range 167, stT250 (i+1)) + stT250 168 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 167
    simpa using h
  have hprev := st250_p167
  have hstep := st250_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p169 : ((1900455038141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT250 (i+1))
      = (∑ i ∈ Finset.range 168, stT250 (i+1)) + stT250 169 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 168
    simpa using h
  have hprev := st250_p168
  have hstep := st250_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p170 : ((174815925827/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT250 (i+1))
      = (∑ i ∈ Finset.range 169, stT250 (i+1)) + stT250 170 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 169
    simpa using h
  have hprev := st250_p169
  have hstep := st250_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p171 : ((8752670083263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT250 (i+1))
      = (∑ i ∈ Finset.range 170, stT250 (i+1)) + stT250 171 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 170
    simpa using h
  have hprev := st250_p170
  have hstep := st250_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p172 : ((1902300576831/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT250 (i+1))
      = (∑ i ∈ Finset.range 171, stT250 (i+1)) + stT250 172 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 171
    simpa using h
  have hprev := st250_p171
  have hstep := st250_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p173 : ((1935330094257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT250 (i+1))
      = (∑ i ∈ Finset.range 172, stT250 (i+1)) + stT250 173 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 172
    simpa using h
  have hprev := st250_p172
  have hstep := st250_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p174 : ((8964185998689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT250 (i+1))
      = (∑ i ∈ Finset.range 173, stT250 (i+1)) + stT250 174 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 173
    simpa using h
  have hprev := st250_p173
  have hstep := st250_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p175 : ((1076298285129/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT250 (i+1))
      = (∑ i ∈ Finset.range 174, stT250 (i+1)) + stT250 175 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 174
    simpa using h
  have hprev := st250_p174
  have hstep := st250_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p176 : ((4608975850519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT250 (i+1))
      = (∑ i ∈ Finset.range 175, stT250 (i+1)) + stT250 176 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 175
    simpa using h
  have hprev := st250_p175
  have hstep := st250_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p177 : ((1218825423/1250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT250 (i+1))
      = (∑ i ∈ Finset.range 176, stT250 (i+1)) + stT250 177 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 176
    simpa using h
  have hprev := st250_p176
  have hstep := st250_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p178 : ((291080426139/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT250 (i+1))
      = (∑ i ∈ Finset.range 177, stT250 (i+1)) + stT250 178 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 177
    simpa using h
  have hprev := st250_p177
  have hstep := st250_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p179 : ((2160424528657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT250 (i+1))
      = (∑ i ∈ Finset.range 178, stT250 (i+1)) + stT250 179 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 178
    simpa using h
  have hprev := st250_p178
  have hstep := st250_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p180 : ((8842288797583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT250 (i+1))
      = (∑ i ∈ Finset.range 179, stT250 (i+1)) + stT250 180 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 179
    simpa using h
  have hprev := st250_p179
  have hstep := st250_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p181 : ((9582747874267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT250 (i+1))
      = (∑ i ∈ Finset.range 180, stT250 (i+1)) + stT250 181 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 180
    simpa using h
  have hprev := st250_p180
  have hstep := st250_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p182 : ((9661585635409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT250 (i+1))
      = (∑ i ∈ Finset.range 181, stT250 (i+1)) + stT250 182 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 181
    simpa using h
  have hprev := st250_p181
  have hstep := st250_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p183 : ((8957008013661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT250 (i+1))
      = (∑ i ∈ Finset.range 182, stT250 (i+1)) + stT250 183 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 182
    simpa using h
  have hprev := st250_p182
  have hstep := st250_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p184 : ((8593274497341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT250 (i+1))
      = (∑ i ∈ Finset.range 183, stT250 (i+1)) + stT250 184 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 183
    simpa using h
  have hprev := st250_p183
  have hstep := st250_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p185 : ((9140266361201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT250 (i+1))
      = (∑ i ∈ Finset.range 184, stT250 (i+1)) + stT250 185 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 184
    simpa using h
  have hprev := st250_p184
  have hstep := st250_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p186 : ((9738693173511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT250 (i+1))
      = (∑ i ∈ Finset.range 185, stT250 (i+1)) + stT250 186 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 185
    simpa using h
  have hprev := st250_p185
  have hstep := st250_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p187 : ((1892708586397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT250 (i+1))
      = (∑ i ∈ Finset.range 186, stT250 (i+1)) + stT250 187 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 186
    simpa using h
  have hprev := st250_p186
  have hstep := st250_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p188 : ((1748435848737/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT250 (i+1))
      = (∑ i ∈ Finset.range 187, stT250 (i+1)) + stT250 188 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 187
    simpa using h
  have hprev := st250_p187
  have hstep := st250_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p189 : ((1734442262203/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT250 (i+1))
      = (∑ i ∈ Finset.range 188, stT250 (i+1)) + stT250 189 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 188
    simpa using h
  have hprev := st250_p188
  have hstep := st250_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p190 : ((9354204456003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT250 (i+1))
      = (∑ i ∈ Finset.range 189, stT250 (i+1)) + stT250 190 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 189
    simpa using h
  have hprev := st250_p189
  have hstep := st250_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p191 : ((9766471596113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT250 (i+1))
      = (∑ i ∈ Finset.range 190, stT250 (i+1)) + stT250 191 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 190
    simpa using h
  have hprev := st250_p190
  have hstep := st250_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p192 : ((372078255729/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT250 (i+1))
      = (∑ i ∈ Finset.range 191, stT250 (i+1)) + stT250 192 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 191
    simpa using h
  have hprev := st250_p191
  have hstep := st250_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p193 : ((8646764034073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT250 (i+1))
      = (∑ i ∈ Finset.range 192, stT250 (i+1)) + stT250 193 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 192
    simpa using h
  have hprev := st250_p192
  have hstep := st250_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p194 : ((8752812174337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT250 (i+1))
      = (∑ i ∈ Finset.range 193, stT250 (i+1)) + stT250 194 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 193
    simpa using h
  have hprev := st250_p193
  have hstep := st250_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p195 : ((9462166058177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT250 (i+1))
      = (∑ i ∈ Finset.range 194, stT250 (i+1)) + stT250 195 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 194
    simpa using h
  have hprev := st250_p194
  have hstep := st250_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p196 : ((2439838404533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT250 (i+1))
      = (∑ i ∈ Finset.range 195, stT250 (i+1)) + stT250 196 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 195
    simpa using h
  have hprev := st250_p195
  have hstep := st250_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p197 : ((144176655067/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT250 (i+1))
      = (∑ i ∈ Finset.range 196, stT250 (i+1)) + stT250 197 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 196
    simpa using h
  have hprev := st250_p196
  have hstep := st250_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p198 : ((4308521467619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT250 (i+1))
      = (∑ i ∈ Finset.range 197, stT250 (i+1)) + stT250 198 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 197
    simpa using h
  have hprev := st250_p197
  have hstep := st250_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p199 : ((43882004009/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT250 (i+1))
      = (∑ i ∈ Finset.range 198, stT250 (i+1)) + stT250 199 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 198
    simpa using h
  have hprev := st250_p198
  have hstep := st250_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p200 : ((4740276610019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT250 (i+1))
      = (∑ i ∈ Finset.range 199, stT250 (i+1)) + stT250 200 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 199
    simpa using h
  have hprev := st250_p199
  have hstep := st250_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p201 : ((4882381056479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT250 (i+1))
      = (∑ i ∈ Finset.range 200, stT250 (i+1)) + stT250 201 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 200
    simpa using h
  have hprev := st250_p200
  have hstep := st250_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p202 : ((2311867984543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT250 (i+1))
      = (∑ i ∈ Finset.range 201, stT250 (i+1)) + stT250 202 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 201
    simpa using h
  have hprev := st250_p201
  have hstep := st250_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p203 : ((8628053275467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT250 (i+1))
      = (∑ i ∈ Finset.range 202, stT250 (i+1)) + stT250 203 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 202
    simpa using h
  have hprev := st250_p202
  have hstep := st250_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p204 : ((8730832427187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT250 (i+1))
      = (∑ i ∈ Finset.range 203, stT250 (i+1)) + stT250 204 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 203
    simpa using h
  have hprev := st250_p203
  have hstep := st250_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p205 : ((9415177887807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT250 (i+1))
      = (∑ i ∈ Finset.range 204, stT250 (i+1)) + stT250 205 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 204
    simpa using h
  have hprev := st250_p204
  have hstep := st250_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p206 : ((978237777753/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT250 (i+1))
      = (∑ i ∈ Finset.range 205, stT250 (i+1)) + stT250 206 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 205
    simpa using h
  have hprev := st250_p205
  have hstep := st250_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p207 : ((4679339343663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT250 (i+1))
      = (∑ i ∈ Finset.range 206, stT250 (i+1)) + stT250 207 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 206
    simpa using h
  have hprev := st250_p206
  have hstep := st250_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p208 : ((4347062470447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT250 (i+1))
      = (∑ i ∈ Finset.range 207, stT250 (i+1)) + stT250 208 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 207
    simpa using h
  have hprev := st250_p207
  have hstep := st250_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p209 : ((8637274960189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT250 (i+1))
      = (∑ i ∈ Finset.range 208, stT250 (i+1)) + stT250 209 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 208
    simpa using h
  have hprev := st250_p208
  have hstep := st250_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p210 : ((2313916589741/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT250 (i+1))
      = (∑ i ∈ Finset.range 209, stT250 (i+1)) + stT250 210 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 209
    simpa using h
  have hprev := st250_p209
  have hstep := st250_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p211 : ((2442392744171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT250 (i+1))
      = (∑ i ∈ Finset.range 210, stT250 (i+1)) + stT250 211 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 210
    simpa using h
  have hprev := st250_p210
  have hstep := st250_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p212 : ((4770514518399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT250 (i+1))
      = (∑ i ∈ Finset.range 211, stT250 (i+1)) + stT250 212 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 211
    simpa using h
  have hprev := st250_p211
  have hstep := st250_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p213 : ((2214211816157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT250 (i+1))
      = (∑ i ∈ Finset.range 212, stT250 (i+1)) + stT250 213 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 212
    simpa using h
  have hprev := st250_p212
  have hstep := st250_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p214 : ((4278212102881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT250 (i+1))
      = (∑ i ∈ Finset.range 213, stT250 (i+1)) + stT250 214 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 213
    simpa using h
  have hprev := st250_p213
  have hstep := st250_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p215 : ((2250303297657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT250 (i+1))
      = (∑ i ∈ Finset.range 214, stT250 (i+1)) + stT250 215 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 214
    simpa using h
  have hprev := st250_p214
  have hstep := st250_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p216 : ((965123486357/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT250 (i+1))
      = (∑ i ∈ Finset.range 215, stT250 (i+1)) + stT250 216 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 215
    simpa using h
  have hprev := st250_p215
  have hstep := st250_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p217 : ((4864963569447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT250 (i+1))
      = (∑ i ∈ Finset.range 216, stT250 (i+1)) + stT250 217 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 216
    simpa using h
  have hprev := st250_p216
  have hstep := st250_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p218 : ((4574073296163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT250 (i+1))
      = (∑ i ∈ Finset.range 217, stT250 (i+1)) + stT250 218 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 217
    simpa using h
  have hprev := st250_p217
  have hstep := st250_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p219 : ((4296460529361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT250 (i+1))
      = (∑ i ∈ Finset.range 218, stT250 (i+1)) + stT250 219 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 218
    simpa using h
  have hprev := st250_p218
  have hstep := st250_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p220 : ((1742017616067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT250 (i+1))
      = (∑ i ∈ Finset.range 219, stT250 (i+1)) + stT250 220 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 219
    simpa using h
  have hprev := st250_p219
  have hstep := st250_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p221 : ((9359723755023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT250 (i+1))
      = (∑ i ∈ Finset.range 220, stT250 (i+1)) + stT250 221 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 220
    simpa using h
  have hprev := st250_p220
  have hstep := st250_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p222 : ((9794324111263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT250 (i+1))
      = (∑ i ∈ Finset.range 221, stT250 (i+1)) + stT250 222 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 221
    simpa using h
  have hprev := st250_p221
  have hstep := st250_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p223 : ((9521734373313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT250 (i+1))
      = (∑ i ∈ Finset.range 222, stT250 (i+1)) + stT250 223 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 222
    simpa using h
  have hprev := st250_p222
  have hstep := st250_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p224 : ((8853911777697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT250 (i+1))
      = (∑ i ∈ Finset.range 223, stT250 (i+1)) + stT250 224 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 223
    simpa using h
  have hprev := st250_p223
  have hstep := st250_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p225 : ((8539988954069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT250 (i+1))
      = (∑ i ∈ Finset.range 224, stT250 (i+1)) + stT250 225 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 224
    simpa using h
  have hprev := st250_p224
  have hstep := st250_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p226 : ((8925588954029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT250 (i+1))
      = (∑ i ∈ Finset.range 225, stT250 (i+1)) + stT250 226 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 225
    simpa using h
  have hprev := st250_p225
  have hstep := st250_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p227 : ((9581689759097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT250 (i+1))
      = (∑ i ∈ Finset.range 226, stT250 (i+1)) + stT250 227 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 226
    simpa using h
  have hprev := st250_p226
  have hstep := st250_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p228 : ((1958063093977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT250 (i+1))
      = (∑ i ∈ Finset.range 227, stT250 (i+1)) + stT250 228 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 227
    simpa using h
  have hprev := st250_p227
  have hstep := st250_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p229 : ((932857149773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT250 (i+1))
      = (∑ i ∈ Finset.range 228, stT250 (i+1)) + stT250 229 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 228
    simpa using h
  have hprev := st250_p228
  have hstep := st250_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p230 : ((8697088248459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT250 (i+1))
      = (∑ i ∈ Finset.range 229, stT250 (i+1)) + stT250 230 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 229
    simpa using h
  have hprev := st250_p229
  have hstep := st250_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p231 : ((8570150227051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT250 (i+1))
      = (∑ i ∈ Finset.range 230, stT250 (i+1)) + stT250 231 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 230
    simpa using h
  have hprev := st250_p230
  have hstep := st250_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p232 : ((9078551538019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT250 (i+1))
      = (∑ i ∈ Finset.range 231, stT250 (i+1)) + stT250 232 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 231
    simpa using h
  have hprev := st250_p231
  have hstep := st250_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p233 : ((9684375993011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT250 (i+1))
      = (∑ i ∈ Finset.range 232, stT250 (i+1)) + stT250 233 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 232
    simpa using h
  have hprev := st250_p232
  have hstep := st250_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p234 : ((9756002785971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT250 (i+1))
      = (∑ i ∈ Finset.range 233, stT250 (i+1)) + stT250 234 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 233
    simpa using h
  have hprev := st250_p233
  have hstep := st250_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p235 : ((9222989978703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT250 (i+1))
      = (∑ i ∈ Finset.range 234, stT250 (i+1)) + stT250 235 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 234
    simpa using h
  have hprev := st250_p234
  have hstep := st250_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p236 : ((4317990072829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT250 (i+1))
      = (∑ i ∈ Finset.range 235, stT250 (i+1)) + stT250 236 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 235
    simpa using h
  have hprev := st250_p235
  have hstep := st250_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p237 : ((4296332759459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT250 (i+1))
      = (∑ i ∈ Finset.range 236, stT250 (i+1)) + stT250 237 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 236
    simpa using h
  have hprev := st250_p236
  have hstep := st250_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p238 : ((182662017619/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT250 (i+1))
      = (∑ i ∈ Finset.range 237, stT250 (i+1)) + stT250 238 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 237
    simpa using h
  have hprev := st250_p237
  have hstep := st250_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p239 : ((194234092559/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT250 (i+1))
      = (∑ i ∈ Finset.range 238, stT250 (i+1)) + stT250 239 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 238
    simpa using h
  have hprev := st250_p238
  have hstep := st250_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p240 : ((9752681423007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT250 (i+1))
      = (∑ i ∈ Finset.range 239, stT250 (i+1)) + stT250 240 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 239
    simpa using h
  have hprev := st250_p239
  have hstep := st250_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p241 : ((460957243023/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT250 (i+1))
      = (∑ i ∈ Finset.range 240, stT250 (i+1)) + stT250 241 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 240
    simpa using h
  have hprev := st250_p240
  have hstep := st250_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p242 : ((1727521230627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT250 (i+1))
      = (∑ i ∈ Finset.range 241, stT250 (i+1)) + stT250 242 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 241
    simpa using h
  have hprev := st250_p241
  have hstep := st250_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p243 : ((1071727954151/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT250 (i+1))
      = (∑ i ∈ Finset.range 242, stT250 (i+1)) + stT250 243 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 242
    simpa using h
  have hprev := st250_p242
  have hstep := st250_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p244 : ((227147158223/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT250 (i+1))
      = (∑ i ∈ Finset.range 243, stT250 (i+1)) + stT250 244 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 243
    simpa using h
  have hprev := st250_p243
  have hstep := st250_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p245 : ((2419857081709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT250 (i+1))
      = (∑ i ∈ Finset.range 244, stT250 (i+1)) + stT250 245 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 244
    simpa using h
  have hprev := st250_p244
  have hstep := st250_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p246 : ((2447382512781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT250 (i+1))
      = (∑ i ∈ Finset.range 245, stT250 (i+1)) + stT250 246 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 245
    simpa using h
  have hprev := st250_p245
  have hstep := st250_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p247 : ((9315442369329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT250 (i+1))
      = (∑ i ∈ Finset.range 246, stT250 (i+1)) + stT250 247 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 246
    simpa using h
  have hprev := st250_p246
  have hstep := st250_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p248 : ((4352560341597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT250 (i+1))
      = (∑ i ∈ Finset.range 247, stT250 (i+1)) + stT250 248 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 247
    simpa using h
  have hprev := st250_p247
  have hstep := st250_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p249 : ((8526987556669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT250 (i+1))
      = (∑ i ∈ Finset.range 248, stT250 (i+1)) + stT250 249 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 248
    simpa using h
  have hprev := st250_p248
  have hstep := st250_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p250 : ((8942629393209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT250 (i+1))
      = (∑ i ∈ Finset.range 249, stT250 (i+1)) + stT250 250 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 249
    simpa using h
  have hprev := st250_p249
  have hstep := st250_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p251 : ((1913445356943/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT250 (i+1))
      = (∑ i ∈ Finset.range 250, stT250 (i+1)) + stT250 251 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 250
    simpa using h
  have hprev := st250_p250
  have hstep := st250_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p252 : ((393247344543/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT250 (i+1))
      = (∑ i ∈ Finset.range 251, stT250 (i+1)) + stT250 252 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 251
    simpa using h
  have hprev := st250_p251
  have hstep := st250_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p253 : ((379937368437/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT250 (i+1))
      = (∑ i ∈ Finset.range 252, stT250 (i+1)) + stT250 253 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 252
    simpa using h
  have hprev := st250_p252
  have hstep := st250_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p254 : ((8871173977197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT250 (i+1))
      = (∑ i ∈ Finset.range 253, stT250 (i+1)) + stT250 254 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 253
    simpa using h
  have hprev := st250_p253
  have hstep := st250_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p255 : ((8509639255297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT250 (i+1))
      = (∑ i ∈ Finset.range 254, stT250 (i+1)) + stT250 255 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 254
    simpa using h
  have hprev := st250_p254
  have hstep := st250_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p256 : ((8731584880297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT250 (i+1))
      = (∑ i ∈ Finset.range 255, stT250 (i+1)) + stT250 256 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 255
    simpa using h
  have hprev := st250_p255
  have hstep := st250_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p257 : ((9338471744827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT250 (i+1))
      = (∑ i ∈ Finset.range 256, stT250 (i+1)) + stT250 257 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 256
    simpa using h
  have hprev := st250_p256
  have hstep := st250_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p258 : ((1959821183867/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT250 (i+1))
      = (∑ i ∈ Finset.range 257, stT250 (i+1)) + stT250 258 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 257
    simpa using h
  have hprev := st250_p257
  have hstep := st250_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p259 : ((388638838517/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT250 (i+1))
      = (∑ i ∈ Finset.range 258, stT250 (i+1)) + stT250 259 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 258
    simpa using h
  have hprev := st250_p258
  have hstep := st250_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p260 : ((9163928658391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT250 (i+1))
      = (∑ i ∈ Finset.range 259, stT250 (i+1)) + stT250 260 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 259
    simpa using h
  have hprev := st250_p259
  have hstep := st250_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p261 : ((8616716207111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT250 (i+1))
      = (∑ i ∈ Finset.range 260, stT250 (i+1)) + stT250 261 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 260
    simpa using h
  have hprev := st250_p260
  have hstep := st250_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p262 : ((266800764039/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT250 (i+1))
      = (∑ i ∈ Finset.range 261, stT250 (i+1)) + stT250 262 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 261
    simpa using h
  have hprev := st250_p261
  have hstep := st250_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p263 : ((4495069261239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT250 (i+1))
      = (∑ i ∈ Finset.range 262, stT250 (i+1)) + stT250 263 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 262
    simpa using h
  have hprev := st250_p262
  have hstep := st250_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p264 : ((1918609393941/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT250 (i+1))
      = (∑ i ∈ Finset.range 263, stT250 (i+1)) + stT250 264 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 263
    simpa using h
  have hprev := st250_p263
  have hstep := st250_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p265 : ((393820544583/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT250 (i+1))
      = (∑ i ∈ Finset.range 264, stT250 (i+1)) + stT250 265 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 264
    simpa using h
  have hprev := st250_p264
  have hstep := st250_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p266 : ((1908374394243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT250 (i+1))
      = (∑ i ∈ Finset.range 265, stT250 (i+1)) + stT250 266 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 265
    simpa using h
  have hprev := st250_p265
  have hstep := st250_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p267 : ((34897931799/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT250 (i+1))
      = (∑ i ∈ Finset.range 266, stT250 (i+1)) + stT250 267 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 266
    simpa using h
  have hprev := st250_p266
  have hstep := st250_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p268 : ((10646320719/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT250 (i+1))
      = (∑ i ∈ Finset.range 267, stT250 (i+1)) + stT250 268 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 267
    simpa using h
  have hprev := st250_p267
  have hstep := st250_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p269 : ((862629770619/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT250 (i+1))
      = (∑ i ∈ Finset.range 268, stT250 (i+1)) + stT250 269 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 268
    simpa using h
  have hprev := st250_p268
  have hstep := st250_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p270 : ((183415726413/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT250 (i+1))
      = (∑ i ∈ Finset.range 269, stT250 (i+1)) + stT250 270 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 269
    simpa using h
  have hprev := st250_p269
  have hstep := st250_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p271 : ((4857362753189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT250 (i+1))
      = (∑ i ∈ Finset.range 270, stT250 (i+1)) + stT250 271 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 270
    simpa using h
  have hprev := st250_p270
  have hstep := st250_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p272 : ((9828448630201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT250 (i+1))
      = (∑ i ∈ Finset.range 271, stT250 (i+1)) + stT250 272 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 271
    simpa using h
  have hprev := st250_p271
  have hstep := st250_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p273 : ((9425397043601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT250 (i+1))
      = (∑ i ∈ Finset.range 272, stT250 (i+1)) + stT250 273 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 272
    simpa using h
  have hprev := st250_p272
  have hstep := st250_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p274 : ((551425570009/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT250 (i+1))
      = (∑ i ∈ Finset.range 273, stT250 (i+1)) + stT250 274 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 273
    simpa using h
  have hprev := st250_p273
  have hstep := st250_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p275 : ((8488248944629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT250 (i+1))
      = (∑ i ∈ Finset.range 274, stT250 (i+1)) + stT250 275 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 274
    simpa using h
  have hprev := st250_p274
  have hstep := st250_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p276 : ((8677212515599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT250 (i+1))
      = (∑ i ∈ Finset.range 275, stT250 (i+1)) + stT250 276 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 275
    simpa using h
  have hprev := st250_p275
  have hstep := st250_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p277 : ((1848432575861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT250 (i+1))
      = (∑ i ∈ Finset.range 276, stT250 (i+1)) + stT250 277 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 276
    simpa using h
  have hprev := st250_p276
  have hstep := st250_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p278 : ((1950458349221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT250 (i+1))
      = (∑ i ∈ Finset.range 277, stT250 (i+1)) + stT250 278 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 277
    simpa using h
  have hprev := st250_p277
  have hstep := st250_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p279 : ((9823625543389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT250 (i+1))
      = (∑ i ∈ Finset.range 278, stT250 (i+1)) + stT250 279 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 278
    simpa using h
  have hprev := st250_p278
  have hstep := st250_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p280 : ((9405439666219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT250 (i+1))
      = (∑ i ∈ Finset.range 279, stT250 (i+1)) + stT250 280 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 279
    simpa using h
  have hprev := st250_p279
  have hstep := st250_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p281 : ((8811574737769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT250 (i+1))
      = (∑ i ∈ Finset.range 280, stT250 (i+1)) + stT250 281 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 280
    simpa using h
  have hprev := st250_p280
  have hstep := st250_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p282 : ((1696319308457/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT250 (i+1))
      = (∑ i ∈ Finset.range 281, stT250 (i+1)) + stT250 282 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 281
    simpa using h
  have hprev := st250_p281
  have hstep := st250_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p283 : ((8655926780107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT250 (i+1))
      = (∑ i ∈ Finset.range 282, stT250 (i+1)) + stT250 283 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 282
    simpa using h
  have hprev := st250_p282
  have hstep := st250_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p284 : ((9204446408477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT250 (i+1))
      = (∑ i ∈ Finset.range 283, stT250 (i+1)) + stT250 284 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 283
    simpa using h
  have hprev := st250_p283
  have hstep := st250_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p285 : ((9727766911341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT250 (i+1))
      = (∑ i ∈ Finset.range 284, stT250 (i+1)) + stT250 285 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 284
    simpa using h
  have hprev := st250_p284
  have hstep := st250_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p286 : ((393985618149/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT250 (i+1))
      = (∑ i ∈ Finset.range 285, stT250 (i+1)) + stT250 286 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 285
    simpa using h
  have hprev := st250_p285
  have hstep := st250_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p287 : ((9485393369139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT250 (i+1))
      = (∑ i ∈ Finset.range 286, stT250 (i+1)) + stT250 287 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 286
    simpa using h
  have hprev := st250_p286
  have hstep := st250_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p288 : ((8896495636787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT250 (i+1))
      = (∑ i ∈ Finset.range 287, stT250 (i+1)) + stT250 288 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 287
    simpa using h
  have hprev := st250_p287
  have hstep := st250_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p289 : ((8499592219327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT250 (i+1))
      = (∑ i ∈ Finset.range 288, stT250 (i+1)) + stT250 289 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 288
    simpa using h
  have hprev := st250_p288
  have hstep := st250_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p290 : ((8571630020047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT250 (i+1))
      = (∑ i ∈ Finset.range 289, stT250 (i+1)) + stT250 290 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 289
    simpa using h
  have hprev := st250_p289
  have hstep := st250_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p291 : ((9059622879387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT250 (i+1))
      = (∑ i ∈ Finset.range 290, stT250 (i+1)) + stT250 291 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 290
    simpa using h
  have hprev := st250_p290
  have hstep := st250_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p292 : ((2405881165443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT250 (i+1))
      = (∑ i ∈ Finset.range 291, stT250 (i+1)) + stT250 292 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 291
    simpa using h
  have hprev := st250_p291
  have hstep := st250_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p293 : ((4937652005517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT250 (i+1))
      = (∑ i ∈ Finset.range 292, stT250 (i+1)) + stT250 293 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 292
    simpa using h
  have hprev := st250_p292
  have hstep := st250_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p294 : ((4822432642797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT250 (i+1))
      = (∑ i ∈ Finset.range 293, stT250 (i+1)) + stT250 294 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 293
    simpa using h
  have hprev := st250_p293
  have hstep := st250_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p295 : ((1818279306579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT250 (i+1))
      = (∑ i ∈ Finset.range 294, stT250 (i+1)) + stT250 295 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 294
    simpa using h
  have hprev := st250_p294
  have hstep := st250_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p296 : ((4294975302027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT250 (i+1))
      = (∑ i ∈ Finset.range 295, stT250 (i+1)) + stT250 296 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 295
    simpa using h
  have hprev := st250_p295
  have hstep := st250_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p297 : ((4238075104487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT250 (i+1))
      = (∑ i ∈ Finset.range 296, stT250 (i+1)) + stT250 297 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 296
    simpa using h
  have hprev := st250_p296
  have hstep := st250_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p298 : ((4411724172747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT250 (i+1))
      = (∑ i ∈ Finset.range 297, stT250 (i+1)) + stT250 298 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 297
    simpa using h
  have hprev := st250_p297
  have hstep := st250_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p299 : ((4699688689279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT250 (i+1))
      = (∑ i ∈ Finset.range 298, stT250 (i+1)) + stT250 299 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 298
    simpa using h
  have hprev := st250_p298
  have hstep := st250_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p300 : ((4911987212479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT250 (i+1))
      = (∑ i ∈ Finset.range 299, stT250 (i+1)) + stT250 300 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 299
    simpa using h
  have hprev := st250_p299
  have hstep := st250_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p301 : ((1964145522891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT250 (i+1))
      = (∑ i ∈ Finset.range 300, stT250 (i+1)) + stT250 301 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 300
    simpa using h
  have hprev := st250_p300
  have hstep := st250_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p302 : ((9394213875819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT250 (i+1))
      = (∑ i ∈ Finset.range 301, stT250 (i+1)) + stT250 302 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 301
    simpa using h
  have hprev := st250_p301
  have hstep := st250_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p303 : ((2205512017941/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT250 (i+1))
      = (∑ i ∈ Finset.range 302, stT250 (i+1)) + stT250 303 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 302
    simpa using h
  have hprev := st250_p302
  have hstep := st250_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p304 : ((2117974901901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT250 (i+1))
      = (∑ i ∈ Finset.range 303, stT250 (i+1)) + stT250 304 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 303
    simpa using h
  have hprev := st250_p303
  have hstep := st250_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p305 : ((171311269413/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT250 (i+1))
      = (∑ i ∈ Finset.range 304, stT250 (i+1)) + stT250 305 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 304
    simpa using h
  have hprev := st250_p304
  have hstep := st250_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p306 : ((9041160841227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT250 (i+1))
      = (∑ i ∈ Finset.range 305, stT250 (i+1)) + stT250 306 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 305
    simpa using h
  have hprev := st250_p305
  have hstep := st250_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p307 : ((9597147743867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT250 (i+1))
      = (∑ i ∈ Finset.range 306, stT250 (i+1)) + stT250 307 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 306
    simpa using h
  have hprev := st250_p306
  have hstep := st250_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p308 : ((395411385977/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT250 (i+1))
      = (∑ i ∈ Finset.range 307, stT250 (i+1)) + stT250 308 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 307
    simpa using h
  have hprev := st250_p307
  have hstep := st250_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p309 : ((9727961746637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT250 (i+1))
      = (∑ i ∈ Finset.range 308, stT250 (i+1)) + stT250 309 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 308
    simpa using h
  have hprev := st250_p308
  have hstep := st250_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p310 : ((9224916099351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT250 (i+1))
      = (∑ i ∈ Finset.range 309, stT250 (i+1)) + stT250 310 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 309
    simpa using h
  have hprev := st250_p309
  have hstep := st250_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p311 : ((1737406615827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT250 (i+1))
      = (∑ i ∈ Finset.range 310, stT250 (i+1)) + stT250 311 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 310
    simpa using h
  have hprev := st250_p310
  have hstep := st250_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p312 : ((4221405169449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT250 (i+1))
      = (∑ i ∈ Finset.range 311, stT250 (i+1)) + stT250 312 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 311
    simpa using h
  have hprev := st250_p311
  have hstep := st250_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p313 : ((8638737618921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT250 (i+1))
      = (∑ i ∈ Finset.range 312, stT250 (i+1)) + stT250 313 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 312
    simpa using h
  have hprev := st250_p312
  have hstep := st250_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p314 : ((9154152192497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT250 (i+1))
      = (∑ i ∈ Finset.range 313, stT250 (i+1)) + stT250 314 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 313
    simpa using h
  have hprev := st250_p313
  have hstep := st250_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p315 : ((9678279516521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT250 (i+1))
      = (∑ i ∈ Finset.range 314, stT250 (i+1)) + stT250 315 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 314
    simpa using h
  have hprev := st250_p314
  have hstep := st250_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p316 : ((9898759244683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT250 (i+1))
      = (∑ i ∈ Finset.range 315, stT250 (i+1)) + stT250 316 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 315
    simpa using h
  have hprev := st250_p315
  have hstep := st250_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p317 : ((387468398139/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT250 (i+1))
      = (∑ i ∈ Finset.range 316, stT250 (i+1)) + stT250 317 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 316
    simpa using h
  have hprev := st250_p316
  have hstep := st250_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p318 : ((9169373308509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT250 (i+1))
      = (∑ i ∈ Finset.range 317, stT250 (i+1)) + stT250 318 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 317
    simpa using h
  have hprev := st250_p317
  have hstep := st250_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p319 : ((4325603167167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT250 (i+1))
      = (∑ i ∈ Finset.range 318, stT250 (i+1)) + stT250 319 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 318
    simpa using h
  have hprev := st250_p318
  have hstep := st250_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p320 : ((4216819577001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT250 (i+1))
      = (∑ i ∈ Finset.range 319, stT250 (i+1)) + stT250 320 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 319
    simpa using h
  have hprev := st250_p319
  have hstep := st250_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p321 : ((8640817554697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT250 (i+1))
      = (∑ i ∈ Finset.range 320, stT250 (i+1)) + stT250 321 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 320
    simpa using h
  have hprev := st250_p320
  have hstep := st250_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p322 : ((1830249150103/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT250 (i+1))
      = (∑ i ∈ Finset.range 321, stT250 (i+1)) + stT250 322 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 321
    simpa using h
  have hprev := st250_p321
  have hstep := st250_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p323 : ((9671502299553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT250 (i+1))
      = (∑ i ∈ Finset.range 322, stT250 (i+1)) + stT250 323 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 322
    simpa using h
  have hprev := st250_p322
  have hstep := st250_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p324 : ((9905917620693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT250 (i+1))
      = (∑ i ∈ Finset.range 323, stT250 (i+1)) + stT250 324 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 323
    simpa using h
  have hprev := st250_p323
  have hstep := st250_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p325 : ((303864099769/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT250 (i+1))
      = (∑ i ∈ Finset.range 324, stT250 (i+1)) + stT250 325 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 324
    simpa using h
  have hprev := st250_p324
  have hstep := st250_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p326 : ((9229327113883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT250 (i+1))
      = (∑ i ∈ Finset.range 325, stT250 (i+1)) + stT250 326 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 325
    simpa using h
  have hprev := st250_p325
  have hstep := st250_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p327 : ((8700622915759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT250 (i+1))
      = (∑ i ∈ Finset.range 326, stT250 (i+1)) + stT250 327 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 326
    simpa using h
  have hprev := st250_p326
  have hstep := st250_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p328 : ((8431181407077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT250 (i+1))
      = (∑ i ∈ Finset.range 327, stT250 (i+1)) + stT250 328 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 327
    simpa using h
  have hprev := st250_p327
  have hstep := st250_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p329 : ((133878929587/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT250 (i+1))
      = (∑ i ∈ Finset.range 328, stT250 (i+1)) + stT250 329 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 328
    simpa using h
  have hprev := st250_p328
  have hstep := st250_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p330 : ((564649925273/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT250 (i+1))
      = (∑ i ∈ Finset.range 329, stT250 (i+1)) + stT250 330 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 329
    simpa using h
  have hprev := st250_p329
  have hstep := st250_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p331 : ((9573532469349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT250 (i+1))
      = (∑ i ∈ Finset.range 330, stT250 (i+1)) + stT250 331 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 330
    simpa using h
  have hprev := st250_p330
  have hstep := st250_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p332 : ((4946414147417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT250 (i+1))
      = (∑ i ∈ Finset.range 331, stT250 (i+1)) + stT250 332 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 331
    simpa using h
  have hprev := st250_p331
  have hstep := st250_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p333 : ((9821276874541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT250 (i+1))
      = (∑ i ∈ Finset.range 332, stT250 (i+1)) + stT250 333 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 332
    simpa using h
  have hprev := st250_p332
  have hstep := st250_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p334 : ((9399339611773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT250 (i+1))
      = (∑ i ∈ Finset.range 333, stT250 (i+1)) + stT250 334 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 333
    simpa using h
  have hprev := st250_p333
  have hstep := st250_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p335 : ((1106730550669/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT250 (i+1))
      = (∑ i ∈ Finset.range 334, stT250 (i+1)) + stT250 335 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 334
    simpa using h
  have hprev := st250_p334
  have hstep := st250_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p336 : ((4237310945841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT250 (i+1))
      = (∑ i ∈ Finset.range 335, stT250 (i+1)) + stT250 336 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 335
    simpa using h
  have hprev := st250_p335
  have hstep := st250_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p337 : ((1057583086439/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT250 (i+1))
      = (∑ i ∈ Finset.range 336, stT250 (i+1)) + stT250 337 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 336
    simpa using h
  have hprev := st250_p336
  have hstep := st250_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p338 : ((1102163425319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT250 (i+1))
      = (∑ i ∈ Finset.range 337, stT250 (i+1)) + stT250 338 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 337
    simpa using h
  have hprev := st250_p337
  have hstep := st250_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p339 : ((9356687555677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT250 (i+1))
      = (∑ i ∈ Finset.range 338, stT250 (i+1)) + stT250 339 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 338
    simpa using h
  have hprev := st250_p338
  have hstep := st250_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p340 : ((1959653456327/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT250 (i+1))
      = (∑ i ∈ Finset.range 339, stT250 (i+1)) + stT250 340 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 339
    simpa using h
  have hprev := st250_p339
  have hstep := st250_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p341 : ((1982997406649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT250 (i+1))
      = (∑ i ∈ Finset.range 340, stT250 (i+1)) + stT250 341 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 340
    simpa using h
  have hprev := st250_p340
  have hstep := st250_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p342 : ((482436492667/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT250 (i+1))
      = (∑ i ∈ Finset.range 341, stT250 (i+1)) + stT250 342 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 341
    simpa using h
  have hprev := st250_p341
  have hstep := st250_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p343 : ((456860357047/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT250 (i+1))
      = (∑ i ∈ Finset.range 342, stT250 (i+1)) + stT250 343 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 342
    simpa using h
  have hprev := st250_p342
  have hstep := st250_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p344 : ((1080117176411/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT250 (i+1))
      = (∑ i ∈ Finset.range 343, stT250 (i+1)) + stT250 344 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 343
    simpa using h
  have hprev := st250_p343
  have hstep := st250_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p345 : ((2102486153547/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT250 (i+1))
      = (∑ i ∈ Finset.range 344, stT250 (i+1)) + stT250 345 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 344
    simpa using h
  have hprev := st250_p344
  have hstep := st250_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p346 : ((8558584854849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT250 (i+1))
      = (∑ i ∈ Finset.range 345, stT250 (i+1)) + stT250 346 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 345
    simpa using h
  have hprev := st250_p345
  have hstep := st250_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p347 : ((1802154451549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT250 (i+1))
      = (∑ i ∈ Finset.range 346, stT250 (i+1)) + stT250 347 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 346
    simpa using h
  have hprev := st250_p346
  have hstep := st250_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p348 : ((9540756887489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT250 (i+1))
      = (∑ i ∈ Finset.range 347, stT250 (i+1)) + stT250 348 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 347
    simpa using h
  have hprev := st250_p347
  have hstep := st250_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p349 : ((1977368054779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT250 (i+1))
      = (∑ i ∈ Finset.range 348, stT250 (i+1)) + stT250 349 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 348
    simpa using h
  have hprev := st250_p348
  have hstep := st250_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p350 : ((9880294505237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT250 (i+1))
      = (∑ i ∈ Finset.range 349, stT250 (i+1)) + stT250 350 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 349
    simpa using h
  have hprev := st250_p349
  have hstep := st250_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p351 : ((9526123798819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT250 (i+1))
      = (∑ i ∈ Finset.range 350, stT250 (i+1)) + stT250 351 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 350
    simpa using h
  have hprev := st250_p350
  have hstep := st250_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p352 : ((359915217627/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT250 (i+1))
      = (∑ i ∈ Finset.range 351, stT250 (i+1)) + stT250 352 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 351
    simpa using h
  have hprev := st250_p351
  have hstep := st250_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p353 : ((8551232596697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT250 (i+1))
      = (∑ i ∈ Finset.range 352, stT250 (i+1)) + stT250 353 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 352
    simpa using h
  have hprev := st250_p352
  have hstep := st250_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p354 : ((4200007679881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT250 (i+1))
      = (∑ i ∈ Finset.range 353, stT250 (i+1)) + stT250 354 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 353
    simpa using h
  have hprev := st250_p353
  have hstep := st250_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p355 : ((4307415404649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT250 (i+1))
      = (∑ i ∈ Finset.range 354, stT250 (i+1)) + stT250 355 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 354
    simpa using h
  have hprev := st250_p354
  have hstep := st250_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p356 : ((4545928284597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT250 (i+1))
      = (∑ i ∈ Finset.range 355, stT250 (i+1)) + stT250 356 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 355
    simpa using h
  have hprev := st250_p355
  have hstep := st250_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p357 : ((4802286394969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT250 (i+1))
      = (∑ i ∈ Finset.range 356, stT250 (i+1)) + stT250 357 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 356
    simpa using h
  have hprev := st250_p356
  have hstep := st250_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p358 : ((4956039627109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT250 (i+1))
      = (∑ i ∈ Finset.range 357, stT250 (i+1)) + stT250 358 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 357
    simpa using h
  have hprev := st250_p357
  have hstep := st250_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p359 : ((4935908250679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT250 (i+1))
      = (∑ i ∈ Finset.range 358, stT250 (i+1)) + stT250 359 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 358
    simpa using h
  have hprev := st250_p358
  have hstep := st250_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p360 : ((9504237585101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT250 (i+1))
      = (∑ i ∈ Finset.range 359, stT250 (i+1)) + stT250 360 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 359
    simpa using h
  have hprev := st250_p359
  have hstep := st250_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p361 : ((1796165264621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT250 (i+1))
      = (∑ i ∈ Finset.range 360, stT250 (i+1)) + stT250 361 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 360
    simpa using h
  have hprev := st250_p360
  have hstep := st250_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p362 : ((854289768447/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT250 (i+1))
      = (∑ i ∈ Finset.range 361, stT250 (i+1)) + stT250 362 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 361
    simpa using h
  have hprev := st250_p361
  have hstep := st250_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p363 : ((839019375231/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT250 (i+1))
      = (∑ i ∈ Finset.range 362, stT250 (i+1)) + stT250 363 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 362
    simpa using h
  have hprev := st250_p362
  have hstep := st250_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p364 : ((4295348468211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT250 (i+1))
      = (∑ i ∈ Finset.range 363, stT250 (i+1)) + stT250 364 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 363
    simpa using h
  have hprev := st250_p363
  have hstep := st250_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p365 : ((9051929432677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT250 (i+1))
      = (∑ i ∈ Finset.range 364, stT250 (i+1)) + stT250 365 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 364
    simpa using h
  have hprev := st250_p364
  have hstep := st250_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p366 : ((9565038945673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT250 (i+1))
      = (∑ i ∈ Finset.range 365, stT250 (i+1)) + stT250 366 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 365
    simpa using h
  have hprev := st250_p365
  have hstep := st250_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p367 : ((9900091876323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT250 (i+1))
      = (∑ i ∈ Finset.range 366, stT250 (i+1)) + stT250 367 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 366
    simpa using h
  have hprev := st250_p366
  have hstep := st250_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p368 : ((9908783277801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT250 (i+1))
      = (∑ i ∈ Finset.range 367, stT250 (i+1)) + stT250 368 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 367
    simpa using h
  have hprev := st250_p367
  have hstep := st250_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p369 : ((9588881662001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT250 (i+1))
      = (∑ i ∈ Finset.range 368, stT250 (i+1)) + stT250 369 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 368
    simpa using h
  have hprev := st250_p368
  have hstep := st250_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p370 : ((9082967451857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT250 (i+1))
      = (∑ i ∈ Finset.range 369, stT250 (i+1)) + stT250 370 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 369
    simpa using h
  have hprev := st250_p369
  have hstep := st250_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p371 : ((1076714604879/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT250 (i+1))
      = (∑ i ∈ Finset.range 370, stT250 (i+1)) + stT250 371 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 370
    simpa using h
  have hprev := st250_p370
  have hstep := st250_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p372 : ((1048195573261/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT250 (i+1))
      = (∑ i ∈ Finset.range 371, stT250 (i+1)) + stT250 372 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 371
    simpa using h
  have hprev := st250_p371
  have hstep := st250_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p373 : ((2124072053657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT250 (i+1))
      = (∑ i ∈ Finset.range 372, stT250 (i+1)) + stT250 373 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 372
    simpa using h
  have hprev := st250_p372
  have hstep := st250_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p374 : ((1779281096289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT250 (i+1))
      = (∑ i ∈ Finset.range 373, stT250 (i+1)) + stT250 374 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 373
    simpa using h
  have hprev := st250_p373
  have hstep := st250_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p375 : ((9412689906899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT250 (i+1))
      = (∑ i ∈ Finset.range 374, stT250 (i+1)) + stT250 375 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 374
    simpa using h
  have hprev := st250_p374
  have hstep := st250_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p376 : ((9824010920119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT250 (i+1))
      = (∑ i ∈ Finset.range 375, stT250 (i+1)) + stT250 376 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 375
    simpa using h
  have hprev := st250_p375
  have hstep := st250_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p377 : ((1991213850361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT250 (i+1))
      = (∑ i ∈ Finset.range 376, stT250 (i+1)) + stT250 377 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 376
    simpa using h
  have hprev := st250_p376
  have hstep := st250_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p378 : ((97543796613/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT250 (i+1))
      = (∑ i ∈ Finset.range 377, stT250 (i+1)) + stT250 378 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 377
    simpa using h
  have hprev := st250_p377
  have hstep := st250_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p379 : ((232634990517/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT250 (i+1))
      = (∑ i ∈ Finset.range 378, stT250 (i+1)) + stT250 379 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 378
    simpa using h
  have hprev := st250_p378
  have hstep := st250_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p380 : ((219956237471/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT250 (i+1))
      = (∑ i ∈ Finset.range 379, stT250 (i+1)) + stT250 380 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 379
    simpa using h
  have hprev := st250_p379
  have hstep := st250_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p381 : ((2111096800541/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT250 (i+1))
      = (∑ i ∈ Finset.range 380, stT250 (i+1)) + stT250 381 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 380
    simpa using h
  have hprev := st250_p380
  have hstep := st250_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p382 : ((4194840547737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT250 (i+1))
      = (∑ i ∈ Finset.range 381, stT250 (i+1)) + stT250 382 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 381
    simpa using h
  have hprev := st250_p381
  have hstep := st250_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p383 : ((4327604375961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT250 (i+1))
      = (∑ i ∈ Finset.range 382, stT250 (i+1)) + stT250 383 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 382
    simpa using h
  have hprev := st250_p382
  have hstep := st250_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p384 : ((2282628764523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT250 (i+1))
      = (∑ i ∈ Finset.range 383, stT250 (i+1)) + stT250 384 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 383
    simpa using h
  have hprev := st250_p383
  have hstep := st250_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p385 : ((9620597219409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT250 (i+1))
      = (∑ i ∈ Finset.range 384, stT250 (i+1)) + stT250 385 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 384
    simpa using h
  have hprev := st250_p384
  have hstep := st250_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p386 : ((9926368013979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT250 (i+1))
      = (∑ i ∈ Finset.range 385, stT250 (i+1)) + stT250 386 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 385
    simpa using h
  have hprev := st250_p385
  have hstep := st250_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p387 : ((9925158190959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT250 (i+1))
      = (∑ i ∈ Finset.range 386, stT250 (i+1)) + stT250 387 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 386
    simpa using h
  have hprev := st250_p386
  have hstep := st250_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p388 : ((9618904358133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT250 (i+1))
      = (∑ i ∈ Finset.range 387, stT250 (i+1)) + stT250 388 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 387
    simpa using h
  have hprev := st250_p387
  have hstep := st250_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p389 : ((913157453271/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT250 (i+1))
      = (∑ i ∈ Finset.range 388, stT250 (i+1)) + stT250 389 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 388
    simpa using h
  have hprev := st250_p388
  have hstep := st250_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p390 : ((3382034253/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT250 (i+1))
      = (∑ i ∈ Finset.range 389, stT250 (i+1)) + stT250 390 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 389
    simpa using h
  have hprev := st250_p389
  have hstep := st250_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p391 : ((419285083839/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT250 (i+1))
      = (∑ i ∈ Finset.range 390, stT250 (i+1)) + stT250 391 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 390
    simpa using h
  have hprev := st250_p390
  have hstep := st250_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p392 : ((421051082073/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT250 (i+1))
      = (∑ i ∈ Finset.range 391, stT250 (i+1)) + stT250 392 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 391
    simpa using h
  have hprev := st250_p391
  have hstep := st250_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p393 : ((2187162214307/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT250 (i+1))
      = (∑ i ∈ Finset.range 392, stT250 (i+1)) + stT250 393 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 392
    simpa using h
  have hprev := st250_p392
  have hstep := st250_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p394 : ((461966130867/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT250 (i+1))
      = (∑ i ∈ Finset.range 393, stT250 (i+1)) + stT250 394 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 393
    simpa using h
  have hprev := st250_p393
  have hstep := st250_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p395 : ((4850852269629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT250 (i+1))
      = (∑ i ∈ Finset.range 394, stT250 (i+1)) + stT250 395 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 394
    simpa using h
  have hprev := st250_p394
  have hstep := st250_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p396 : ((1244651918007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT250 (i+1))
      = (∑ i ∈ Finset.range 395, stT250 (i+1)) + stT250 396 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 395
    simpa using h
  have hprev := st250_p395
  have hstep := st250_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p397 : ((4954280504779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT250 (i+1))
      = (∑ i ∈ Finset.range 396, stT250 (i+1)) + stT250 397 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 396
    simpa using h
  have hprev := st250_p396
  have hstep := st250_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p398 : ((149621293397/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT250 (i+1))
      = (∑ i ∈ Finset.range 397, stT250 (i+1)) + stT250 398 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 397
    simpa using h
  have hprev := st250_p397
  have hstep := st250_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p399 : ((2271725127977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT250 (i+1))
      = (∑ i ∈ Finset.range 398, stT250 (i+1)) + stT250 399 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 398
    simpa using h
  have hprev := st250_p398
  have hstep := st250_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p400 : ((862798059407/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT250 (i+1))
      = (∑ i ∈ Finset.range 399, stT250 (i+1)) + stT250 400 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 399
    simpa using h
  have hprev := st250_p399
  have hstep := st250_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p401 : ((2092989748739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT250 (i+1))
      = (∑ i ∈ Finset.range 400, stT250 (i+1)) + stT250 401 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 400
    simpa using h
  have hprev := st250_p400
  have hstep := st250_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p402 : ((2103495004241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT250 (i+1))
      = (∑ i ∈ Finset.range 401, stT250 (i+1)) + stT250 402 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 401
    simpa using h
  have hprev := st250_p401
  have hstep := st250_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p403 : ((4368481888537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT250 (i+1))
      = (∑ i ∈ Finset.range 402, stT250 (i+1)) + stT250 403 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 402
    simpa using h
  have hprev := st250_p402
  have hstep := st250_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p404 : ((2304878984529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT250 (i+1))
      = (∑ i ∈ Finset.range 403, stT250 (i+1)) + stT250 404 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 403
    simpa using h
  have hprev := st250_p403
  have hstep := st250_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p405 : ((1936468564217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT250 (i+1))
      = (∑ i ∈ Finset.range 404, stT250 (i+1)) + stT250 405 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 404
    simpa using h
  have hprev := st250_p404
  have hstep := st250_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p406 : ((995509194741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT250 (i+1))
      = (∑ i ∈ Finset.range 405, stT250 (i+1)) + stT250 406 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 405
    simpa using h
  have hprev := st250_p405
  have hstep := st250_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p407 : ((77645863269/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT250 (i+1))
      = (∑ i ∈ Finset.range 406, stT250 (i+1)) + stT250 407 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 406
    simpa using h
  have hprev := st250_p406
  have hstep := st250_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p408 : ((2410095370599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT250 (i+1))
      = (∑ i ∈ Finset.range 407, stT250 (i+1)) + stT250 408 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 407
    simpa using h
  have hprev := st250_p407
  have hstep := st250_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p409 : ((9169791873813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT250 (i+1))
      = (∑ i ∈ Finset.range 408, stT250 (i+1)) + stT250 409 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 408
    simpa using h
  have hprev := st250_p408
  have hstep := st250_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p410 : ((4348855382549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT250 (i+1))
      = (∑ i ∈ Finset.range 409, stT250 (i+1)) + stT250 410 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 409
    simpa using h
  have hprev := st250_p409
  have hstep := st250_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p411 : ((4196951034269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT250 (i+1))
      = (∑ i ∈ Finset.range 410, stT250 (i+1)) + stT250 411 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 410
    simpa using h
  have hprev := st250_p410
  have hstep := st250_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p412 : ((8366323174503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT250 (i+1))
      = (∑ i ∈ Finset.range 411, stT250 (i+1)) + stT250 412 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 411
    simpa using h
  have hprev := st250_p411
  have hstep := st250_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p413 : ((344941378739/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT250 (i+1))
      = (∑ i ∈ Finset.range 412, stT250 (i+1)) + stT250 413 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 412
    simpa using h
  have hprev := st250_p412
  have hstep := st250_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p414 : ((1814609100747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT250 (i+1))
      = (∑ i ∈ Finset.range 413, stT250 (i+1)) + stT250 414 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 413
    simpa using h
  have hprev := st250_p413
  have hstep := st250_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p415 : ((382213561231/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT250 (i+1))
      = (∑ i ∈ Finset.range 414, stT250 (i+1)) + stT250 415 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 414
    simpa using h
  have hprev := st250_p414
  have hstep := st250_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p416 : ((1980169572929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT250 (i+1))
      = (∑ i ∈ Finset.range 415, stT250 (i+1)) + stT250 416 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 415
    simpa using h
  have hprev := st250_p415
  have hstep := st250_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p417 : ((1997874748739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT250 (i+1))
      = (∑ i ∈ Finset.range 416, stT250 (i+1)) + stT250 417 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 416
    simpa using h
  have hprev := st250_p416
  have hstep := st250_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p418 : ((9791259264359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT250 (i+1))
      = (∑ i ∈ Finset.range 417, stT250 (i+1)) + stT250 418 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 417
    simpa using h
  have hprev := st250_p417
  have hstep := st250_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p419 : ((75011233927/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT250 (i+1))
      = (∑ i ∈ Finset.range 418, stT250 (i+1)) + stT250 419 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 418
    simpa using h
  have hprev := st250_p418
  have hstep := st250_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p420 : ((1777761889021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT250 (i+1))
      = (∑ i ∈ Finset.range 419, stT250 (i+1)) + stT250 420 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 419
    simpa using h
  have hprev := st250_p419
  have hstep := st250_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p421 : ((8496135605147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT250 (i+1))
      = (∑ i ∈ Finset.range 420, stT250 (i+1)) + stT250 421 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 420
    simpa using h
  have hprev := st250_p420
  have hstep := st250_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p422 : ((8332100967937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT250 (i+1))
      = (∑ i ∈ Finset.range 421, stT250 (i+1)) + stT250 422 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 421
    simpa using h
  have hprev := st250_p421
  have hstep := st250_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p423 : ((8451452895673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT250 (i+1))
      = (∑ i ∈ Finset.range 422, stT250 (i+1)) + stT250 423 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 422
    simpa using h
  have hprev := st250_p422
  have hstep := st250_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p424 : ((8812533550377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT250 (i+1))
      = (∑ i ∈ Finset.range 423, stT250 (i+1)) + stT250 424 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 423
    simpa using h
  have hprev := st250_p423
  have hstep := st250_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p425 : ((116157440277/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT250 (i+1))
      = (∑ i ∈ Finset.range 424, stT250 (i+1)) + stT250 425 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 424
    simpa using h
  have hprev := st250_p424
  have hstep := st250_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p426 : ((77840661341/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT250 (i+1))
      = (∑ i ∈ Finset.range 425, stT250 (i+1)) + stT250 426 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 425
    simpa using h
  have hprev := st250_p425
  have hstep := st250_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p427 : ((2494774654909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT250 (i+1))
      = (∑ i ∈ Finset.range 426, stT250 (i+1)) + stT250 427 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 426
    simpa using h
  have hprev := st250_p426
  have hstep := st250_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p428 : ((4978854770693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT250 (i+1))
      = (∑ i ∈ Finset.range 427, stT250 (i+1)) + stT250 428 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 427
    simpa using h
  have hprev := st250_p427
  have hstep := st250_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p429 : ((1209269408507/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT250 (i+1))
      = (∑ i ∈ Finset.range 428, stT250 (i+1)) + stT250 429 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 428
    simpa using h
  have hprev := st250_p428
  have hstep := st250_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p430 : ((4611490627787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT250 (i+1))
      = (∑ i ∈ Finset.range 429, stT250 (i+1)) + stT250 430 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 429
    simpa using h
  have hprev := st250_p429
  have hstep := st250_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p431 : ((4376422814737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT250 (i+1))
      = (∑ i ∈ Finset.range 430, stT250 (i+1)) + stT250 431 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 430
    simpa using h
  have hprev := st250_p430
  have hstep := st250_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p432 : ((2104319752097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT250 (i+1))
      = (∑ i ∈ Finset.range 431, stT250 (i+1)) + stT250 432 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 431
    simpa using h
  have hprev := st250_p431
  have hstep := st250_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p433 : ((4162368062029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT250 (i+1))
      = (∑ i ∈ Finset.range 432, stT250 (i+1)) + stT250 433 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 432
    simpa using h
  have hprev := st250_p432
  have hstep := st250_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p434 : ((4252041584239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT250 (i+1))
      = (∑ i ∈ Finset.range 433, stT250 (i+1)) + stT250 434 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 433
    simpa using h
  have hprev := st250_p433
  have hstep := st250_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p435 : ((4448187979687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT250 (i+1))
      = (∑ i ∈ Finset.range 434, stT250 (i+1)) + stT250 435 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 434
    simpa using h
  have hprev := st250_p434
  have hstep := st250_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p436 : ((9374912054843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT250 (i+1))
      = (∑ i ∈ Finset.range 435, stT250 (i+1)) + stT250 436 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 435
    simpa using h
  have hprev := st250_p435
  have hstep := st250_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p437 : ((9786573935411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT250 (i+1))
      = (∑ i ∈ Finset.range 436, stT250 (i+1)) + stT250 437 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 436
    simpa using h
  have hprev := st250_p436
  have hstep := st250_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p438 : ((10000823704067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT250 (i+1))
      = (∑ i ∈ Finset.range 437, stT250 (i+1)) + stT250 438 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 437
    simpa using h
  have hprev := st250_p437
  have hstep := st250_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p439 : ((9950729025027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT250 (i+1))
      = (∑ i ∈ Finset.range 438, stT250 (i+1)) + stT250 439 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 438
    simpa using h
  have hprev := st250_p438
  have hstep := st250_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p440 : ((386127813591/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT250 (i+1))
      = (∑ i ∈ Finset.range 439, stT250 (i+1)) + stT250 440 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 439
    simpa using h
  have hprev := st250_p439
  have hstep := st250_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p441 : ((57516083847/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT250 (i+1))
      = (∑ i ∈ Finset.range 440, stT250 (i+1)) + stT250 441 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 440
    simpa using h
  have hprev := st250_p440
  have hstep := st250_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p442 : ((1092522943073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT250 (i+1))
      = (∑ i ∈ Finset.range 441, stT250 (i+1)) + stT250 442 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 441
    simpa using h
  have hprev := st250_p441
  have hstep := st250_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p443 : ((8409786198009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT250 (i+1))
      = (∑ i ∈ Finset.range 442, stT250 (i+1)) + stT250 443 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 442
    simpa using h
  have hprev := st250_p442
  have hstep := st250_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p444 : ((1662610931751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT250 (i+1))
      = (∑ i ∈ Finset.range 443, stT250 (i+1)) + stT250 444 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 443
    simpa using h
  have hprev := st250_p443
  have hstep := st250_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p445 : ((423939347667/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT250 (i+1))
      = (∑ i ∈ Finset.range 444, stT250 (i+1)) + stT250 445 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 444
    simpa using h
  have hprev := st250_p444
  have hstep := st250_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p446 : ((8855027598289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT250 (i+1))
      = (∑ i ∈ Finset.range 445, stT250 (i+1)) + stT250 446 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 445
    simpa using h
  have hprev := st250_p445
  have hstep := st250_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p447 : ((9325964473831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT250 (i+1))
      = (∑ i ∈ Finset.range 446, stT250 (i+1)) + stT250 447 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 446
    simpa using h
  have hprev := st250_p446
  have hstep := st250_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p448 : ((4873992215063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT250 (i+1))
      = (∑ i ∈ Finset.range 447, stT250 (i+1)) + stT250 448 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 447
    simpa using h
  have hprev := st250_p447
  have hstep := st250_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p449 : ((9993517290601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT250 (i+1))
      = (∑ i ∈ Finset.range 448, stT250 (i+1)) + stT250 449 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 448
    simpa using h
  have hprev := st250_p448
  have hstep := st250_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p450 : ((9989277474031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT250 (i+1))
      = (∑ i ∈ Finset.range 449, stT250 (i+1)) + stT250 450 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 449
    simpa using h
  have hprev := st250_p449
  have hstep := st250_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p451 : ((9737576447689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT250 (i+1))
      = (∑ i ∈ Finset.range 450, stT250 (i+1)) + stT250 451 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 450
    simpa using h
  have hprev := st250_p450
  have hstep := st250_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p452 : ((186293506859/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT250 (i+1))
      = (∑ i ∈ Finset.range 451, stT250 (i+1)) + stT250 452 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 451
    simpa using h
  have hprev := st250_p451
  have hstep := st250_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p453 : ((4423562643833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT250 (i+1))
      = (∑ i ∈ Finset.range 452, stT250 (i+1)) + stT250 453 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 452
    simpa using h
  have hprev := st250_p452
  have hstep := st250_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p454 : ((4236817920247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT250 (i+1))
      = (∑ i ∈ Finset.range 453, stT250 (i+1)) + stT250 454 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 453
    simpa using h
  have hprev := st250_p453
  have hstep := st250_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p455 : ((830400797947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT250 (i+1))
      = (∑ i ∈ Finset.range 454, stT250 (i+1)) + stT250 455 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 454
    simpa using h
  have hprev := st250_p454
  have hstep := st250_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p456 : ((4193606348577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT250 (i+1))
      = (∑ i ∈ Finset.range 455, stT250 (i+1)) + stT250 456 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 455
    simpa using h
  have hprev := st250_p455
  have hstep := st250_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p457 : ((4348922874197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT250 (i+1))
      = (∑ i ∈ Finset.range 456, stT250 (i+1)) + stT250 457 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 456
    simpa using h
  have hprev := st250_p456
  have hstep := st250_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p458 : ((1143061303659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT250 (i+1))
      = (∑ i ∈ Finset.range 457, stT250 (i+1)) + stT250 458 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 457
    simpa using h
  have hprev := st250_p457
  have hstep := st250_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p459 : ((1199629348339/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT250 (i+1))
      = (∑ i ∈ Finset.range 458, stT250 (i+1)) + stT250 459 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 458
    simpa using h
  have hprev := st250_p458
  have hstep := st250_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p460 : ((310148649687/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT250 (i+1))
      = (∑ i ∈ Finset.range 459, stT250 (i+1)) + stT250 460 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 459
    simpa using h
  have hprev := st250_p459
  have hstep := st250_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p461 : ((5016955675637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT250 (i+1))
      = (∑ i ∈ Finset.range 460, stT250 (i+1)) + stT250 461 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 460
    simpa using h
  have hprev := st250_p460
  have hstep := st250_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p462 : ((1978828330697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT250 (i+1))
      = (∑ i ∈ Finset.range 461, stT250 (i+1)) + stT250 462 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 461
    simpa using h
  have hprev := st250_p461
  have hstep := st250_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p463 : ((1909262236629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT250 (i+1))
      = (∑ i ∈ Finset.range 462, stT250 (i+1)) + stT250 463 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 462
    simpa using h
  have hprev := st250_p462
  have hstep := st250_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p464 : ((4545019030073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT250 (i+1))
      = (∑ i ∈ Finset.range 463, stT250 (i+1)) + stT250 464 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 463
    simpa using h
  have hprev := st250_p463
  have hstep := st250_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p465 : ((865478005457/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT250 (i+1))
      = (∑ i ∈ Finset.range 464, stT250 (i+1)) + stT250 465 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 464
    simpa using h
  have hprev := st250_p464
  have hstep := st250_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p466 : ((1045375248151/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT250 (i+1))
      = (∑ i ∈ Finset.range 465, stT250 (i+1)) + stT250 466 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 465
    simpa using h
  have hprev := st250_p465
  have hstep := st250_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p467 : ((8295928485693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT250 (i+1))
      = (∑ i ∈ Finset.range 466, stT250 (i+1)) + stT250 467 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 466
    simpa using h
  have hprev := st250_p466
  have hstep := st250_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p468 : ((8471365765943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT250 (i+1))
      = (∑ i ∈ Finset.range 467, stT250 (i+1)) + stT250 468 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 467
    simpa using h
  have hprev := st250_p467
  have hstep := st250_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p469 : ((2209886350277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT250 (i+1))
      = (∑ i ∈ Finset.range 468, stT250 (i+1)) + stT250 469 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 468
    simpa using h
  have hprev := st250_p468
  have hstep := st250_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p470 : ((2324430442667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT250 (i+1))
      = (∑ i ∈ Finset.range 469, stT250 (i+1)) + stT250 470 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 469
    simpa using h
  have hprev := st250_p469
  have hstep := st250_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p471 : ((9719176536043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT250 (i+1))
      = (∑ i ∈ Finset.range 470, stT250 (i+1)) + stT250 471 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 470
    simpa using h
  have hprev := st250_p470
  have hstep := st250_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p472 : ((9988308186091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT250 (i+1))
      = (∑ i ∈ Finset.range 471, stT250 (i+1)) + stT250 472 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 471
    simpa using h
  have hprev := st250_p471
  have hstep := st250_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p473 : ((10032118849691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT250 (i+1))
      = (∑ i ∈ Finset.range 472, stT250 (i+1)) + stT250 473 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 472
    simpa using h
  have hprev := st250_p472
  have hstep := st250_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p474 : ((9839567611383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT250 (i+1))
      = (∑ i ∈ Finset.range 473, stT250 (i+1)) + stT250 474 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 473
    simpa using h
  have hprev := st250_p473
  have hstep := st250_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p475 : ((9463831921911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT250 (i+1))
      = (∑ i ∈ Finset.range 474, stT250 (i+1)) + stT250 475 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 474
    simpa using h
  have hprev := st250_p474
  have hstep := st250_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p476 : ((9007139315511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT250 (i+1))
      = (∑ i ∈ Finset.range 475, stT250 (i+1)) + stT250 476 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 475
    simpa using h
  have hprev := st250_p475
  have hstep := st250_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p477 : ((1074082991781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT250 (i+1))
      = (∑ i ∈ Finset.range 476, stT250 (i+1)) + stT250 477 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 476
    simpa using h
  have hprev := st250_p476
  have hstep := st250_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p478 : ((4165642608509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT250 (i+1))
      = (∑ i ∈ Finset.range 477, stT250 (i+1)) + stT250 478 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 477
    simpa using h
  have hprev := st250_p477
  have hstep := st250_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p479 : ((4146060502469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT250 (i+1))
      = (∑ i ∈ Finset.range 478, stT250 (i+1)) + stT250 479 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 478
    simpa using h
  have hprev := st250_p478
  have hstep := st250_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p480 : ((4242352768679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT250 (i+1))
      = (∑ i ∈ Finset.range 479, stT250 (i+1)) + stT250 480 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 479
    simpa using h
  have hprev := st250_p479
  have hstep := st250_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p481 : ((4428563640959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT250 (i+1))
      = (∑ i ∈ Finset.range 480, stT250 (i+1)) + stT250 481 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 480
    simpa using h
  have hprev := st250_p480
  have hstep := st250_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p482 : ((9310508565517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT250 (i+1))
      = (∑ i ∈ Finset.range 481, stT250 (i+1)) + stT250 482 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 481
    simpa using h
  have hprev := st250_p481
  have hstep := st250_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p483 : ((9725497716027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT250 (i+1))
      = (∑ i ∈ Finset.range 482, stT250 (i+1)) + stT250 483 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 482
    simpa using h
  have hprev := st250_p482
  have hstep := st250_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p484 : ((9993731084157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT250 (i+1))
      = (∑ i ∈ Finset.range 483, stT250 (i+1)) + stT250 484 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 483
    simpa using h
  have hprev := st250_p483
  have hstep := st250_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p485 : ((10045941650789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT250 (i+1))
      = (∑ i ∈ Finset.range 484, stT250 (i+1)) + stT250 485 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 484
    simpa using h
  have hprev := st250_p484
  have hstep := st250_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p486 : ((9869416144019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT250 (i+1))
      = (∑ i ∈ Finset.range 485, stT250 (i+1)) + stT250 486 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 485
    simpa using h
  have hprev := st250_p485
  have hstep := st250_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p487 : ((9510652976339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT250 (i+1))
      = (∑ i ∈ Finset.range 486, stT250 (i+1)) + stT250 487 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 486
    simpa using h
  have hprev := st250_p486
  have hstep := st250_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p488 : ((9062664636137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT250 (i+1))
      = (∑ i ∈ Finset.range 487, stT250 (i+1)) + stT250 488 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 487
    simpa using h
  have hprev := st250_p487
  have hstep := st250_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p489 : ((8640591545833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT250 (i+1))
      = (∑ i ∈ Finset.range 488, stT250 (i+1)) + stT250 489 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 488
    simpa using h
  have hprev := st250_p488
  have hstep := st250_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p490 : ((8352052200247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT250 (i+1))
      = (∑ i ∈ Finset.range 489, stT250 (i+1)) + stT250 490 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 489
    simpa using h
  have hprev := st250_p489
  have hstep := st250_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p491 : ((8269878783551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT250 (i+1))
      = (∑ i ∈ Finset.range 490, stT250 (i+1)) + stT250 491 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 490
    simpa using h
  have hprev := st250_p490
  have hstep := st250_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p492 : ((8414065865933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT250 (i+1))
      = (∑ i ∈ Finset.range 491, stT250 (i+1)) + stT250 492 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 491
    simpa using h
  have hprev := st250_p491
  have hstep := st250_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p493 : ((8747360158751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT250 (i+1))
      = (∑ i ∈ Finset.range 492, stT250 (i+1)) + stT250 493 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 492
    simpa using h
  have hprev := st250_p492
  have hstep := st250_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p494 : ((9185307861099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT250 (i+1))
      = (∑ i ∈ Finset.range 493, stT250 (i+1)) + stT250 494 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 493
    simpa using h
  have hprev := st250_p493
  have hstep := st250_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p495 : ((9617917987167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT250 (i+1))
      = (∑ i ∈ Finset.range 494, stT250 (i+1)) + stT250 495 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 494
    simpa using h
  have hprev := st250_p494
  have hstep := st250_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p496 : ((2484347347407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT250 (i+1))
      = (∑ i ∈ Finset.range 495, stT250 (i+1)) + stT250 496 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 495
    simpa using h
  have hprev := st250_p495
  have hstep := st250_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p497 : ((10064848446339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT250 (i+1))
      = (∑ i ∈ Finset.range 496, stT250 (i+1)) + stT250 497 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 496
    simpa using h
  have hprev := st250_p496
  have hstep := st250_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p498 : ((9969517312199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT250 (i+1))
      = (∑ i ∈ Finset.range 497, stT250 (i+1)) + stT250 498 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 497
    simpa using h
  have hprev := st250_p497
  have hstep := st250_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p499 : ((1935144064579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT250 (i+1))
      = (∑ i ∈ Finset.range 498, stT250 (i+1)) + stT250 499 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 498
    simpa using h
  have hprev := st250_p498
  have hstep := st250_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_p500 : ((9256286809361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT250 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT250 (i+1))
      = (∑ i ∈ Finset.range 499, stT250 (i+1)) + stT250 500 := by
    have h := Finset.sum_range_succ (fun i => stT250 (i+1)) 499
    simpa using h
  have hprev := st250_p499
  have hstep := st250_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st250_s500 :
    |Real.sin (((250 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))
      - ((86773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 6967809/10000000) (δ := 783/62500000) (ψ := -540941/500000) 250 247
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 250`** (evaluated boundary). -/
theorem station_250_sign : hardyG ((((250:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 250 500 (by norm_num) (by norm_num)
    ((-540941/500000 : ℚ) : ℝ)
  have hchain := st250_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT250 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((250 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-540941/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st250_c500
  have hsinb := abs_le.mp st250_s500
  have hbdy_lo : ((-728339550961/23585000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((250 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-540941/500000 : ℚ) : ℝ))) / 2
          - ((((250:ℕ)):ℝ))
            * Real.sin (((250 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-540941/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((250:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((250:ℝ) * Real.log (500:ℝ) - ((-540941/500000 : ℚ) : ℝ))) / 2
        - ((250:ℝ)) * Real.sin ((250:ℝ) * Real.log (500:ℝ) - ((-540941/500000 : ℚ) : ℝ))
        ≥ ((-172633219/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((250:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-172633219/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-172633219/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-172633219/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((250:ℕ)):ℝ))+1) * (((((250:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1238070144491/2500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((9256286809361/10000000000000 : ℚ) : ℝ) + ((-728339550961/23585000000000 : ℚ) : ℝ)
      - ((1238070144491/2500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-540941/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((250:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-540941/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((250:ℕ)):ℝ)))).re
      - Real.sin ((-540941/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((250:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((250:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((250:ℕ)):ℝ))
      = (((((250:ℕ)):ℝ)) * (Real.log ((((250:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((250:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_250
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
  have hθwin : |(((-540941/500000 : ℚ) : ℝ) + ((54:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((250:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((250:ℕ)):ℝ)))
    (φ := ((-540941/500000 : ℚ) : ℝ) + ((54:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-540941/500000 : ℚ) : ℝ) + ((54:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-540941/500000 : ℚ)) : ℝ) - Real.pi) + ((54:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-540941/500000 : ℚ)) : ℝ) - Real.pi) 54).1,
    (cos_sin_shift ((((-540941/500000 : ℚ)) : ℝ) - Real.pi) 54).2]
  exact cos_sin_flip ((-540941/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_250_sign
end AxiomAudit
