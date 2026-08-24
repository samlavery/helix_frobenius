import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 132` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT132 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((132 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))

theorem st132_c1 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((27381/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78577/625000) (δ := 201/1000000000) (ψ := -502893/1000000) 132 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t1 : ((438071/500000 : ℚ) : ℝ) ≤ stT132 1 := by
  have hc : ((438071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438071/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((438071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c2 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-156939/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5623657/10000000) (δ := 6609/1000000000) (ψ := -502893/1000000) 132 15
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t2 : ((-554907364601/1250000000000 : ℚ) : ℝ) ≤ stT132 2 := by
  have hc : ((-313903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554907364601/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-313903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c3 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((106973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62903/250000) (δ := 6667/1000000000) (ψ := -502893/1000000) 132 23
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t3 : ((308775547213/1000000000000 : ℚ) : ℝ) ≤ stT132 3 := by
  have hc : ((106963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308775547213/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((106963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c4 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((285399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3203433/10000000) (δ := 6693/1000000000) (ψ := -502893/1000000) 132 29
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t4 : ((285349/2000000 : ℚ) : ℝ) ≤ stT132 4 := by
  have hc : ((285349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285349/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((285349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c5 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((31113/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339799/2000000) (δ := 3323/500000000) (ψ := -502893/1000000) 132 34
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t5 : ((27826518397/80000000000 : ℚ) : ℝ) ≤ stT132 5 := by
  have hc : ((31111/40000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27826518397/80000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((31111/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c6 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-174211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4364753/10000000) (δ := 3337/500000000) (ψ := -502893/1000000) 132 38
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t6 : ((-711417570063/10000000000000 : ℚ) : ℝ) ≤ stT132 6 := by
  have hc : ((-174261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-711417570063/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-174261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c7 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((121189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19341/312500) (δ := 6607/1000000000) (ψ := -502893/1000000) 132 41
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t7 : ((458027653941/1250000000000 : ℚ) : ℝ) ≤ stT132 7 := by
  have hc : ((484731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458027653941/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((484731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c8 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((19931/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5746/15625) (δ := 3343/500000000) (ψ := -502893/1000000) 132 44
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t8 : ((70431352893/2000000000000 : ℚ) : ℝ) ≤ stT132 8 := by
  have hc : ((19921/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70431352893/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((19921/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c9 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((60749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 235939/625000) (δ := 1683/250000000) (ψ := -502893/1000000) 132 46
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t9 : ((202329979767/10000000000000 : ℚ) : ℝ) ≤ stT132 9 := by
  have hc : ((60699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202329979767/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((60699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c10 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-958139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3564031/5000000) (δ := 6657/1000000000) (ψ := -502893/1000000) 132 48
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t10 : ((-1515029997271/5000000000000 : ℚ) : ℝ) ≤ stT132 10 := by
  have hc : ((-958189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1515029997271/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-958189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c11 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-96221/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3582251/5000000) (δ := 169/25000000) (ψ := -502893/1000000) 132 50
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t11 : ((-72533089941/250000000000 : ℚ) : ℝ) ≤ stT132 11 := by
  have hc : ((-48113/50000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72533089941/250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-48113/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c12 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-106253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4462337/10000000) (δ := 1657/250000000) (ψ := -502893/1000000) 132 52
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t12 : ((-4793722329/78125000000 : ℚ) : ℝ) ≤ stT132 12 := by
  have hc : ((-53139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4793722329/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-53139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c13 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((488403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269749/5000000) (δ := 6789/1000000000) (ψ := -502893/1000000) 132 54
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t13 : ((1354516383/5000000000 : ℚ) : ℝ) ≤ stT132 13 := by
  have hc : ((244189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1354516383/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((244189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c14 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-49499/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1499957/2000000) (δ := 1651/250000000) (ψ := -502893/1000000) 132 56
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t14 : ((-264596704839/1000000000000 : ℚ) : ℝ) ≤ stT132 14 := by
  have hc : ((-99003/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264596704839/1000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-99003/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c15 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((492273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -440091/10000000) (δ := 6711/1000000000) (ψ := -502893/1000000) 132 57
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t15 : ((39718075907/156250000000 : ℚ) : ℝ) ≤ stT132 15 := by
  have hc : ((61531/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39718075907/156250000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((61531/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c16 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-2349/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102993/200000) (δ := 1357/200000000) (ψ := -502893/1000000) 132 58
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t16 : ((-23492509397/200000000000 : ℚ) : ℝ) ≤ stT132 16 := by
  have hc : ((-9397/20000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23492509397/200000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-9397/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c17 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-803569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3130079/5000000) (δ := 829/125000000) (ψ := -502893/1000000) 132 60
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t17 : ((-1949062966983/10000000000000 : ℚ) : ℝ) ≤ stT132 17 := by
  have hc : ((-803619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1949062966983/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-803619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c18 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((322583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3105849/10000000) (δ := 6739/1000000000) (ψ := -502893/1000000) 132 61
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t18 : ((380108688363/5000000000000 : ℚ) : ℝ) ≤ stT132 18 := by
  have hc : ((322533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380108688363/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((322533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c19 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((46271/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -971637/10000000) (δ := 1689/250000000) (ψ := -502893/1000000) 132 62
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t19 : ((212294406309/1000000000000 : ℚ) : ℝ) ≤ stT132 19 := by
  have hc : ((92537/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212294406309/1000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((92537/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c20 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((248779/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 247189/10000000) (δ := 6649/1000000000) (ψ := -502893/1000000) 132 63
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t20 : ((1112517122711/5000000000000 : ℚ) : ℝ) ≤ stT132 20 := by
  have hc : ((497533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1112517122711/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((497533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c21 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((967411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79999/1250000) (δ := 6661/1000000000) (ψ := -502893/1000000) 132 64
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t21 : ((1055476946129/5000000000000 : ℚ) : ℝ) ≤ stT132 21 := by
  have hc : ((967361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1055476946129/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((967361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c22 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((993571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 283629/10000000) (δ := 423/62500000) (ψ := -502893/1000000) 132 65
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t22 : ((2118193726647/10000000000000 : ℚ) : ℝ) ≤ stT132 22 := by
  have hc : ((993521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2118193726647/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((993521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c23 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((190943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -755241/10000000) (δ := 841/125000000) (ψ := -502893/1000000) 132 66
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t23 : ((49765349919/250000000000 : ℚ) : ℝ) ≤ stT132 23 := by
  have hc : ((190933/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49765349919/250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((190933/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c24 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((56743/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302317/1250000) (δ := 331/50000000) (ψ := -502893/1000000) 132 67
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t24 : ((57907965929/500000000000 : ℚ) : ℝ) ≤ stT132 24 := by
  have hc : ((28369/50000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57907965929/500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((28369/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c25 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-287197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4655239/10000000) (δ := 669/100000000) (ψ := -502893/1000000) 132 68
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t25 : ((-574494287247/10000000000000 : ℚ) : ℝ) ≤ stT132 25 := by
  have hc : ((-287247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-574494287247/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-287247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c26 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-246249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7420371/10000000) (δ := 6797/1000000000) (ψ := -502893/1000000) 132 69
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t26 : ((-482958695863/2500000000000 : ℚ) : ℝ) ≤ stT132 26 := by
  have hc : ((-492523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482958695863/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-492523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c27 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-13389/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 629241/1250000) (δ := 6797/1000000000) (ψ := -502893/1000000) 132 69
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t27 : ((-412322414749/5000000000000 : ℚ) : ℝ) ≤ stT132 27 := by
  have hc : ((-214249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-412322414749/5000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-214249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c28 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((862341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265461/2000000) (δ := 6699/1000000000) (ψ := -502893/1000000) 132 70
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t28 : ((814788251101/5000000000000 : ℚ) : ℝ) ≤ stT132 28 := by
  have hc : ((862291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((814788251101/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((862291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c29 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((108873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2800529/10000000) (δ := 6611/1000000000) (ψ := -502893/1000000) 132 71
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t29 : ((404297664113/5000000000000 : ℚ) : ℝ) ≤ stT132 29 := by
  have hc : ((217721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404297664113/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((217721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c30 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-12217/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7320997/10000000) (δ := 3359/500000000) (ψ := -502893/1000000) 132 72
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t30 : ((-89224924411/500000000000 : ℚ) : ℝ) ≤ stT132 30 := by
  have hc : ((-97741/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89224924411/500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-97741/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c31 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((170097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 349967/1000000) (δ := 3359/500000000) (ψ := -502893/1000000) 132 72
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t31 : ((305413424491/10000000000000 : ℚ) : ℝ) ≤ stT132 31 := by
  have hc : ((170047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305413424491/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((170047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c32 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((769659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1731223/10000000) (δ := 6777/1000000000) (ψ := -502893/1000000) 132 73
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t32 : ((680244311747/5000000000000 : ℚ) : ℝ) ≤ stT132 32 := by
  have hc : ((769609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680244311747/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((769609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c33 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-243543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3642279/5000000) (δ := 667/100000000) (ψ := -502893/1000000) 132 74
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t33 : ((-847951625247/5000000000000 : ℚ) : ℝ) ≤ stT132 33 := by
  have hc : ((-487111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-847951625247/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-487111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c34 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((517583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 641733/2500000) (δ := 667/100000000) (ψ := -502893/1000000) 132 74
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t34 : ((177512266401/2000000000000 : ℚ) : ℝ) ≤ stT132 34 := by
  have hc : ((517533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177512266401/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((517533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c35 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((14027/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893789/2500000) (δ := 83/12500000) (ψ := -502893/1000000) 132 75
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t35 : ((2962687347/125000000000 : ℚ) : ℝ) ≤ stT132 35 := by
  have hc : ((7011/50000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2962687347/125000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((7011/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c36 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-328827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5721241/10000000) (δ := 83/12500000) (ψ := -502893/1000000) 132 75
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t36 : ((-137021694071/1250000000000 : ℚ) : ℝ) ≤ stT132 36 := by
  have hc : ((-82213/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137021694071/1250000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-82213/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c37 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((929397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236263/2500000) (δ := 6747/1000000000) (ψ := -502893/1000000) 132 76
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t37 : ((1527836245183/10000000000000 : ℚ) : ℝ) ≤ stT132 37 := by
  have hc : ((929347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1527836245183/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((929347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c38 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -785251/1000000) (δ := 6749/1000000000) (ψ := -502893/1000000) 132 77
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t38 : ((-6489184443/40000000000 : ℚ) : ℝ) ≤ stT132 38 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6489184443/40000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c39 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((958881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143881/2000000) (δ := 6749/1000000000) (ψ := -502893/1000000) 132 77
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t39 : ((1535357862511/10000000000000 : ℚ) : ℝ) ≤ stT132 39 := by
  have hc : ((958831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1535357862511/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((958831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c40 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-883217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1658421/2500000) (δ := 6641/1000000000) (ψ := -502893/1000000) 132 78
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t40 : ((-1396567901113/10000000000000 : ℚ) : ℝ) ≤ stT132 40 := by
  have hc : ((-883267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1396567901113/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-883267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c41 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((410981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757437/5000000) (δ := 6641/1000000000) (ψ := -502893/1000000) 132 78
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t41 : ((160451297643/1250000000000 : ℚ) : ℝ) ≤ stT132 41 := by
  have hc : ((102739/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160451297643/1250000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((102739/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c42 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-159791/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6240881/10000000) (δ := 6669/1000000000) (ψ := -502893/1000000) 132 79
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t42 : ((-123289188117/1000000000000 : ℚ) : ℝ) ≤ stT132 42 := by
  have hc : ((-159801/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123289188117/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-159801/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c43 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((163967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190523/1250000) (δ := 6669/1000000000) (ψ := -502893/1000000) 132 79
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t43 : ((50006393129/400000000000 : ℚ) : ℝ) ≤ stT132 43 := by
  have hc : ((163957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50006393129/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((163957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c44 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-876287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1649311/2500000) (δ := 847/125000000) (ψ := -502893/1000000) 132 80
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t44 : ((-1321127978709/10000000000000 : ℚ) : ℝ) ≤ stT132 44 := by
  have hc : ((-876337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1321127978709/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-876337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c45 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((473423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40939/500000) (δ := 847/125000000) (ψ := -502893/1000000) 132 80
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t45 : ((352849802989/2500000000000 : ℚ) : ℝ) ≤ stT132 45 := by
  have hc : ((236699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352849802989/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((236699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c46 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-498103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7636147/10000000) (δ := 21/3125000) (ψ := -502893/1000000) 132 81
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t46 : ((-2295155893/15625000000 : ℚ) : ℝ) ≤ stT132 46 := by
  have hc : ((-31133/31250 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2295155893/15625000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-31133/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c47 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((488421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134767/2500000) (δ := 21/3125000) (ψ := -502893/1000000) 132 81
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t47 : ((178099584251/1250000000000 : ℚ) : ℝ) ≤ stT132 47 := by
  have hc : ((122099/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178099584251/1250000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((122099/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c48 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-104683/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3204277/5000000) (δ := 21/3125000) (ψ := -502893/1000000) 132 81
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t48 : ((-37776487727/312500000000 : ℚ) : ℝ) ≤ stT132 48 := by
  have hc : ((-418757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37776487727/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-418757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c49 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((13549/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2495073/10000000) (δ := 6613/1000000000) (ψ := -502893/1000000) 132 82
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t49 : ((77415691061/1000000000000 : ℚ) : ℝ) ≤ stT132 49 := by
  have hc : ((54191/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77415691061/1000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((54191/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c50 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-24447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4171851/10000000) (δ := 6613/1000000000) (ψ := -502893/1000000) 132 82
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t50 : ((-34590967333/2500000000000 : ℚ) : ℝ) ≤ stT132 50 := by
  have hc : ((-48919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34590967333/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-48919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c51 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-416603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2500627/5000000) (δ := 6697/1000000000) (ψ := -502893/1000000) 132 83
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t51 : ((-583431279493/10000000000000 : ℚ) : ℝ) ≤ stT132 51 := by
  have hc : ((-416653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583431279493/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-416653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c52 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((13216/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1406719/10000000) (δ := 6697/1000000000) (ψ := -502893/1000000) 132 83
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t52 : ((2345754189/20000000000 : ℚ) : ℝ) ≤ stT132 52 := by
  have hc : ((422887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2345754189/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((422887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c53 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-498959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61541/80000) (δ := 6697/1000000000) (ψ := -502893/1000000) 132 83
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t53 : ((-42837963519/312500000000 : ℚ) : ℝ) ≤ stT132 53 := by
  have hc : ((-62373/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42837963519/312500000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-62373/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c54 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((184823/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -923473/5000000) (δ := 3399/500000000) (ψ := -502893/1000000) 132 84
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t54 : ((502990236567/5000000000000 : ℚ) : ℝ) ≤ stT132 54 := by
  have hc : ((369621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502990236567/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((369621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c55 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-112269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4208257/10000000) (δ := 3399/500000000) (ψ := -502893/1000000) 132 84
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t55 : ((-378627349/25000000000 : ℚ) : ℝ) ≤ stT132 55 := by
  have hc : ((-112319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378627349/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-112319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c56 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-605699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5553601/10000000) (δ := 6691/1000000000) (ψ := -502893/1000000) 132 85
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t56 : ((-809466628943/10000000000000 : ℚ) : ℝ) ≤ stT132 56 := by
  have hc : ((-605749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-809466628943/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-605749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c57 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((198681/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287267/10000000) (δ := 6691/1000000000) (ψ := -502893/1000000) 132 85
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t57 : ((65786524243/500000000000 : ℚ) : ℝ) ≤ stT132 57 := by
  have hc : ((198671/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65786524243/500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((198671/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c58 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-46533/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6026561/10000000) (δ := 6691/1000000000) (ψ := -502893/1000000) 132 85
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t58 : ((-97767931157/1000000000000 : ℚ) : ℝ) ≤ stT132 58 := by
  have hc : ((-372289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97767931157/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-372289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c59 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-5661/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16161/40000) (δ := 6619/1000000000) (ψ := -502893/1000000) 132 86
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t59 : ((-2951254441/500000000000 : ℚ) : ℝ) ≤ stT132 59 := by
  have hc : ((-22669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2951254441/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-22669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c60 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((823957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506093/10000000) (δ := 6619/1000000000) (ψ := -502893/1000000) 132 86
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t60 : ((531829496779/5000000000000 : ℚ) : ℝ) ≤ stT132 60 := by
  have hc : ((823907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531829496779/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((823907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c61 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-936849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3480381/5000000) (δ := 6619/1000000000) (ψ := -502893/1000000) 132 86
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t61 : ((-1199576435731/10000000000000 : ℚ) : ℝ) ≤ stT132 61 := by
  have hc : ((-936899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1199576435731/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-936899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c62 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((54143/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -845309/2500000) (δ := 3363/500000000) (ψ := -502893/1000000) 132 87
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t62 : ((137491578261/5000000000000 : ℚ) : ℝ) ≤ stT132 62 := by
  have hc : ((108261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137491578261/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((108261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c63 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((36257/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118681/625000) (δ := 3363/500000000) (ψ := -502893/1000000) 132 87
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t63 : ((91352711429/1000000000000 : ℚ) : ℝ) ≤ stT132 63 := by
  have hc : ((72509/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91352711429/1000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((72509/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c64 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-14912/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1419167/2000000) (δ := 3363/500000000) (ψ := -502893/1000000) 132 87
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t64 : ((-596511727209/5000000000000 : ℚ) : ℝ) ≤ stT132 64 := by
  have hc : ((-477209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596511727209/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-477209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c65 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((34329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3495743/10000000) (δ := 677/100000000) (ψ := -502893/1000000) 132 88
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t65 : ((42567468693/2000000000000 : ℚ) : ℝ) ≤ stT132 65 := by
  have hc : ((34319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42567468693/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((34319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c66 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((81561/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385633/2500000) (δ := 677/100000000) (ψ := -502893/1000000) 132 88
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t66 : ((12548552773/125000000000 : ℚ) : ℝ) ≤ stT132 66 := by
  have hc : ((20389/25000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12548552773/125000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((20389/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c67 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-428963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6505039/10000000) (δ := 677/100000000) (ψ := -502893/1000000) 132 88
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t67 : ((-26204624733/250000000000 : ℚ) : ℝ) ≤ stT132 67 := by
  have hc : ((-107247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26204624733/250000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-107247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c68 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-154163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4313941/10000000) (δ := 6663/1000000000) (ψ := -502893/1000000) 132 89
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t68 : ((-187010866627/10000000000000 : ℚ) : ℝ) ≤ stT132 68 := by
  have hc : ((-154213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187010866627/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-154213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c69 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((489887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 503663/10000000) (δ := 6663/1000000000) (ψ := -502893/1000000) 132 89
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t69 : ((147431071899/1250000000000 : ℚ) : ℝ) ≤ stT132 69 := by
  have hc : ((244931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147431071899/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((244931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c70 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-252757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2625967/5000000) (δ := 6663/1000000000) (ψ := -502893/1000000) 132 89
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t70 : ((-151066188539/2500000000000 : ℚ) : ℝ) ≤ stT132 70 := by
  have hc : ((-126391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151066188539/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-126391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c71 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-168433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5775111/10000000) (δ := 831/125000000) (ψ := -502893/1000000) 132 90
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t71 : ((-199908087381/2500000000000 : ℚ) : ℝ) ≤ stT132 71 := by
  have hc : ((-336891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199908087381/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-336891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c72 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((178867/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72477/625000) (δ := 831/125000000) (ψ := -502893/1000000) 132 90
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t72 : ((210784941927/2000000000000 : ℚ) : ℝ) ≤ stT132 72 := by
  have hc : ((178857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210784941927/2000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((178857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c73 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((42461/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3392157/10000000) (δ := 831/125000000) (ψ := -502893/1000000) 132 90
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t73 : ((49685117361/2000000000000 : ℚ) : ℝ) ≤ stT132 73 := by
  have hc : ((42451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49685117361/2000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((42451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c74 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-999937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3912979/5000000) (δ := 1351/200000000) (ψ := -502893/1000000) 132 91
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t74 : ((-1162461887799/10000000000000 : ℚ) : ℝ) ≤ stT132 74 := by
  have hc : ((-999987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1162461887799/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-999987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c75 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((13167/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -679267/2000000) (δ := 1351/200000000) (ψ := -502893/1000000) 132 91
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t75 : ((1216026117/50000000000 : ℚ) : ℝ) ≤ stT132 75 := by
  have hc : ((105311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1216026117/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((105311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c76 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((924973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 974581/10000000) (δ := 1351/200000000) (ψ := -502893/1000000) 132 91
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t76 : ((530479412497/5000000000000 : ℚ) : ℝ) ≤ stT132 76 := by
  have hc : ((924923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530479412497/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((924923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c77 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-129509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2644187/5000000) (δ := 1351/200000000) (ψ := -502893/1000000) 132 91
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t77 : ((-147603478529/2500000000000 : ℚ) : ℝ) ≤ stT132 77 := by
  have hc : ((-259043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147603478529/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-259043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c78 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-194863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1540367/2500000) (δ := 6741/1000000000) (ψ := -502893/1000000) 132 92
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t78 : ((-220653241389/2500000000000 : ℚ) : ℝ) ≤ stT132 78 := by
  have hc : ((-389751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220653241389/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-389751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c79 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((708773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -978799/5000000) (δ := 6741/1000000000) (ψ := -502893/1000000) 132 92
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t79 : ((797375033901/10000000000000 : ℚ) : ℝ) ≤ stT132 79 := by
  have hc : ((708723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((797375033901/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((708723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c80 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((319591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1096703/5000000) (δ := 6741/1000000000) (ψ := -502893/1000000) 132 92
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t80 : ((178642666839/2500000000000 : ℚ) : ℝ) ≤ stT132 80 := by
  have hc : ((159783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178642666839/2500000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((159783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c81 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-811279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6292831/10000000) (δ := 6741/1000000000) (ψ := -502893/1000000) 132 92
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t81 : ((-112684673481/1250000000000 : ℚ) : ℝ) ≤ stT132 81 := by
  have hc : ((-811329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112684673481/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-811329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c82 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-544341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5365999/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 93
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t82 : ((-150294922889/2500000000000 : ℚ) : ℝ) ≤ stT132 82 := by
  have hc : ((-544391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150294922889/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-544391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c83 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((427207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1365937/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 93
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t83 : ((117223226211/1250000000000 : ℚ) : ℝ) ≤ stT132 83 := by
  have hc : ((213591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117223226211/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((213591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c84 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((20439/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2586193/10000000) (δ := 13369/1000000000) (ψ := -502893/1000000) 132 93
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t84 : ((22298585893/400000000000 : ℚ) : ℝ) ≤ stT132 84 := by
  have hc : ((20437/40000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22298585893/400000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((20437/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c85 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-106893/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6491561/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 93
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t85 : ((-463794368841/5000000000000 : ℚ) : ℝ) ≤ stT132 85 := by
  have hc : ((-427597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463794368841/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-427597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c86 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-67653/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2678361/5000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 94
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t86 : ((-36479431867/625000000000 : ℚ) : ℝ) ≤ stT132 86 := by
  have hc : ((-270637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36479431867/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-270637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c87 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((40791/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12333/80000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 94
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t87 : ((5466230039/62500000000 : ℚ) : ℝ) ≤ stT132 87 := by
  have hc : ((81577/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5466230039/62500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((81577/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c88 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((125581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1114923/5000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 94
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t88 : ((133859062713/2000000000000 : ℚ) : ℝ) ≤ stT132 88 := by
  have hc : ((125571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133859062713/2000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((125571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c89 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-72613/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5958681/10000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 94
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t89 : ((-19243733691/250000000000 : ℚ) : ℝ) ≤ stT132 89 := by
  have hc : ((-36309/50000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19243733691/250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-36309/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c90 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-753941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6062093/10000000) (δ := 53/7812500) (ψ := -502893/1000000) 132 95
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t90 : ((-794776635163/10000000000000 : ℚ) : ℝ) ≤ stT132 90 := by
  have hc : ((-753991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-794776635163/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-753991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c91 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((568383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2415643/10000000) (δ := 13219/1000000000) (ψ := -502893/1000000) 132 95
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t91 : ((148943597643/2500000000000 : ℚ) : ℝ) ≤ stT132 91 := by
  have hc : ((568333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148943597643/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((568333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c92 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((444331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37217/312500) (δ := 53/7812500) (ψ := -502893/1000000) 132 95
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t92 : ((57902624379/625000000000 : ℚ) : ℝ) ≤ stT132 92 := by
  have hc : ((222153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57902624379/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((222153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c93 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-326521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4758541/10000000) (δ := 53/7812500) (ψ := -502893/1000000) 132 95
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t93 : ((-42329806449/1250000000000 : ℚ) : ℝ) ≤ stT132 93 := by
  have hc : ((-326571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42329806449/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-326571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c94 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-984969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3709987/5000000) (δ := 839/125000000) (ψ := -502893/1000000) 132 96
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t94 : ((-507985133509/5000000000000 : ℚ) : ℝ) ≤ stT132 94 := by
  have hc : ((-985019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507985133509/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-985019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c95 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-89/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3927881/10000000) (δ := 839/125000000) (ψ := -502893/1000000) 132 96
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t95 : ((-208273737/5000000000000 : ℚ) : ℝ) ≤ stT132 95 := by
  have hc : ((-203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208273737/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c96 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((245551/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14761/312500) (δ := 839/125000000) (ψ := -502893/1000000) 132 96
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t96 : ((25060150387/250000000000 : ℚ) : ℝ) ≤ stT132 96 := by
  have hc : ((491077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25060150387/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((491077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c97 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((381897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736843/2500000) (δ := 839/125000000) (ψ := -502893/1000000) 132 96
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t97 : ((193853412031/5000000000000 : ℚ) : ℝ) ≤ stT132 97 := by
  have hc : ((381847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193853412031/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((381847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c98 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-820343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6332017/10000000) (δ := 839/125000000) (ψ := -502893/1000000) 132 96
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t98 : ((-828722450129/10000000000000 : ℚ) : ℝ) ≤ stT132 98 := by
  have hc : ((-820393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-828722450129/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-820393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c99 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-372143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3012827/5000000) (δ := 1321/200000000) (ψ := -502893/1000000) 132 97
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t99 : ((-23377686399/312500000000 : ℚ) : ℝ) ≤ stT132 99 := by
  have hc : ((-46521/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23377686399/312500000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-46521/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c100 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((468131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541811/2000000) (δ := 1321/200000000) (ψ := -502893/1000000) 132 97
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t100 : ((468080531919/10000000000000 : ℚ) : ℝ) ≤ stT132 100 := by
  have hc : ((468081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468080531919/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((468081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c101 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((194741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 574577/10000000) (δ := 1321/200000000) (ψ := -502893/1000000) 132 97
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t101 : ((193764550047/2000000000000 : ℚ) : ℝ) ≤ stT132 101 := by
  have hc : ((194731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193764550047/2000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((194731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c102 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((40451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 956459/2500000) (δ := 1321/200000000) (ψ := -502893/1000000) 132 97
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t102 : ((40002928947/10000000000000 : ℚ) : ℝ) ≤ stT132 102 := by
  have hc : ((40401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40002928947/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((40401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c103 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-59259/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7045349/10000000) (δ := 1321/200000000) (ψ := -502893/1000000) 132 97
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t103 : ((-46714199701/500000000000 : ℚ) : ℝ) ≤ stT132 103 := by
  have hc : ((-474097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46714199701/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-474097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c104 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-290061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5474187/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 98
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t104 : ((-142226409983/2500000000000 : ℚ) : ℝ) ≤ stT132 104 := by
  have hc : ((-145043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142226409983/2500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-145043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c105 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((120127/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579063/2500000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 98
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t105 : ((1172221803/20000000000 : ℚ) : ℝ) ≤ stT132 105 := by
  have hc : ((120117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1172221803/20000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((120117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c106 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((3791/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811719/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 98
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t106 : ((1840973589/20000000000 : ℚ) : ℝ) ≤ stT132 106 := by
  have hc : ((9477/10000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1840973589/20000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((9477/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c107 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((1331/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3910353/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 98
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t107 : ((79816141/125000000000 : ℚ) : ℝ) ≤ stT132 107 := by
  have hc : ((1321/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79816141/125000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((1321/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c108 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-234883/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1396029/2000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 98
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t108 : ((-452056859541/5000000000000 : ℚ) : ℝ) ≤ stT132 108 := by
  have hc : ((-469791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452056859541/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-469791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c109 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-323537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5686341/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 99
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t109 : ((-154958209887/2500000000000 : ℚ) : ℝ) ≤ stT132 109 := by
  have hc : ((-161781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154958209887/2500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-161781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c110 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((480961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334077/1250000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 99
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t110 : ((229265181941/5000000000000 : ℚ) : ℝ) ≤ stT132 110 := by
  have hc : ((480911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229265181941/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((480911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c111 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((99213/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313851/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 99
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t111 : ((11770495957/125000000000 : ℚ) : ℝ) ≤ stT132 111 := by
  have hc : ((12401/12500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11770495957/125000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((12401/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c112 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((129217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3273489/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 99
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t112 : ((15259367739/625000000000 : ℚ) : ℝ) ≤ stT132 112 := by
  have hc : ((16149/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15259367739/625000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((16149/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c113 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-790697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6206859/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 99
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t113 : ((-743872308587/10000000000000 : ℚ) : ℝ) ≤ stT132 113 := by
  have hc : ((-790747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-743872308587/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-790747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c114 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-175117/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3296803/5000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 100
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t114 : ((-82010748211/1000000000000 : ℚ) : ℝ) ≤ stT132 114 := by
  have hc : ((-175127/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82010748211/1000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-175127/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c115 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((5381/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742297/2000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 100
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t115 : ((5014889949/625000000000 : ℚ) : ℝ) ≤ stT132 115 := by
  have hc : ((43023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5014889949/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((43023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c116 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((471087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170869/2000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 100
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t116 : ((54671220189/625000000000 : ℚ) : ℝ) ≤ stT132 116 := by
  have hc : ((235531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54671220189/625000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((235531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c117 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((87863/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1978309/10000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 100
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t117 : ((649788523/10000000000 : ℚ) : ℝ) ≤ stT132 117 := by
  have hc : ((351427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((649788523/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((351427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c118 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-337199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119671/250000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 100
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t118 : ((-12418519927/400000000000 : ℚ) : ℝ) ≤ stT132 118 := by
  have hc : ((-337249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12418519927/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-337249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c119 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-99363/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1892911/2500000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 100
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t119 : ((-11386318279/125000000000 : ℚ) : ℝ) ≤ stT132 119 := by
  have hc : ((-12421/12500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11386318279/125000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-12421/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c120 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-136821/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268739/500000) (δ := 6627/1000000000) (ψ := -502893/1000000) 132 101
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t120 : ((-249822667957/5000000000000 : ℚ) : ℝ) ≤ stT132 120 := by
  have hc : ((-273667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249822667957/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-273667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c121 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((61711/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164761/625000) (δ := 6627/1000000000) (ψ := -502893/1000000) 132 101
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t121 : ((22438068471/500000000000 : ℚ) : ℝ) ≤ stT132 121 := by
  have hc : ((246819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22438068471/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((246819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c122 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((999489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79889/10000000) (δ := 6627/1000000000) (ψ := -502893/1000000) 132 101
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t122 : ((904849094723/10000000000000 : ℚ) : ℝ) ≤ stT132 122 := by
  have hc : ((999439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904849094723/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((999439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c123 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((445099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1386889/5000000) (δ := 6627/1000000000) (ψ := -502893/1000000) 132 101
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t123 : ((401286886781/10000000000000 : ℚ) : ℝ) ≤ stT132 123 := by
  have hc : ((445049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401286886781/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((445049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c124 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-285427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2722927/5000000) (δ := 6627/1000000000) (ψ := -502893/1000000) 132 101
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t124 : ((-64085900801/1250000000000 : ℚ) : ℝ) ≤ stT132 124 := by
  have hc : ((-71363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64085900801/1250000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-71363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c125 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-995299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7611483/10000000) (δ := 3367/500000000) (ψ := -502893/1000000) 132 102
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t125 : ((-222567003843/2500000000000 : ℚ) : ℝ) ≤ stT132 125 := by
  have hc : ((-995349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222567003843/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-995349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c126 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-409581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4981977/10000000) (δ := 3367/500000000) (ψ := -502893/1000000) 132 102
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t126 : ((-364928378601/10000000000000 : ℚ) : ℝ) ≤ stT132 126 := by
  have hc : ((-409631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364928378601/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-409631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c127 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((291119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1186647/5000000) (δ := 3367/500000000) (ψ := -502893/1000000) 132 102
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t127 : ((32288000933/625000000000 : ℚ) : ℝ) ≤ stT132 127 := by
  have hc : ((145547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32288000933/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((145547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c128 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((498153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107481/5000000) (δ := 3367/500000000) (ψ := -502893/1000000) 132 102
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t128 : ((27517929439/312500000000 : ℚ) : ℝ) ≤ stT132 128 := by
  have hc : ((31133/31250 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27517929439/312500000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((31133/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c129 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((441761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173943/625000) (δ := 3367/500000000) (ψ := -502893/1000000) 132 102
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t129 : ((7778088999/200000000000 : ℚ) : ℝ) ≤ stT132 129 := by
  have hc : ((441711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7778088999/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((441711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c130 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-266331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1332837/2500000) (δ := 3367/500000000) (ψ := -502893/1000000) 132 102
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t130 : ((-58402481751/1250000000000 : ℚ) : ℝ) ≤ stT132 130 := by
  have hc : ((-66589/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58402481751/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-66589/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c131 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-999997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7847859/10000000) (δ := 3381/500000000) (ψ := -502893/1000000) 132 103
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t131 : ((-174749212827/2000000000000 : ℚ) : ℝ) ≤ stT132 131 := by
  have hc : ((-1000047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174749212827/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-1000047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c132 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-535027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5338341/10000000) (δ := 3381/500000000) (ψ := -502893/1000000) 132 103
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t132 : ((-465725134953/10000000000000 : ℚ) : ℝ) ≤ stT132 132 := by
  have hc : ((-535077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465725134953/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-535077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c133 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((418407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569553/2000000) (δ := 3381/500000000) (ψ := -502893/1000000) 132 103
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t133 : ((362761119913/10000000000000 : ℚ) : ℝ) ≤ stT132 133 := by
  have hc : ((418357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362761119913/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((418357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c134 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((12359/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7517/200000) (δ := 13241/1000000000) (ψ := -502893/1000000) 132 103
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t134 : ((21352009389/250000000000 : ℚ) : ℝ) ≤ stT132 134 := by
  have hc : ((98867/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21352009389/250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((98867/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c135 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((674083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2077683/10000000) (δ := 3381/500000000) (ψ := -502893/1000000) 132 103
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t135 : ((290057294923/5000000000000 : ℚ) : ℝ) ≤ stT132 135 := by
  have hc : ((674033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290057294923/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((674033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c136 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-58077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1128279/2500000) (δ := 3381/500000000) (ψ := -502893/1000000) 132 103
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t136 : ((-99622679247/5000000000000 : ℚ) : ℝ) ≤ stT132 136 := by
  have hc : ((-116179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99622679247/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-116179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c137 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-46629/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6930729/10000000) (δ := 3381/500000000) (ψ := -502893/1000000) 132 103
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t137 : ((-39839995077/500000000000 : ℚ) : ℝ) ≤ stT132 137 := by
  have hc : ((-93263/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39839995077/500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-93263/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c138 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-415277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6377243/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t138 : ((-176764367307/2500000000000 : ℚ) : ℝ) ≤ stT132 138 := by
  have hc : ((-207651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176764367307/2500000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-207651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c139 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-13509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249659/625000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t139 : ((-5739694963/2500000000000 : ℚ) : ℝ) ≤ stT132 139 := by
  have hc : ((-6767/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5739694963/2500000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-6767/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c140 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((795129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1628939/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t140 : ((335982098583/5000000000000 : ℚ) : ℝ) ≤ stT132 140 := by
  have hc : ((795079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335982098583/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((795079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c141 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((239709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 719803/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t141 : ((403721294343/5000000000000 : ℚ) : ℝ) ≤ stT132 141 := by
  have hc : ((479393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((403721294343/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((479393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c142 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((171451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3051979/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t142 : ((71928721053/2500000000000 : ℚ) : ℝ) ≤ stT132 142 := by
  have hc : ((85713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71928721053/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((85713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c143 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-544941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5367787/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t143 : ((-455744908813/10000000000000 : ℚ) : ℝ) ≤ stT132 143 := by
  have hc : ((-544991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-455744908813/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-544991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c144 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-997217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 306697/400000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 104
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t144 : ((-415528249089/5000000000000 : ℚ) : ℝ) ≤ stT132 144 := by
  have hc : ((-997267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415528249089/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-997267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c145 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-334147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5756773/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t145 : ((-13875740413/250000000000 : ℚ) : ℝ) ≤ stT132 145 := by
  have hc : ((-83543/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13875740413/250000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-83543/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c146 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((174413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -872179/2500000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t146 : ((28860738123/2000000000000 : ℚ) : ℝ) ≤ stT132 146 := by
  have hc : ((174363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28860738123/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((174363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c147 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((880221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1236169/10000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t147 : ((362976359203/5000000000000 : ℚ) : ℝ) ≤ stT132 147 := by
  have hc : ((880171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362976359203/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((880171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c148 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((184177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250283/2500000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t148 : ((75692084499/1000000000000 : ℚ) : ℝ) ≤ stT132 148 := by
  have hc : ((184167/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75692084499/1000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((184167/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c149 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((138871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 644677/2000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t149 : ((56873473713/2500000000000 : ℚ) : ℝ) ≤ stT132 149 := by
  have hc : ((69423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56873473713/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((69423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c150 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-282937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2715361/5000000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t150 : ((-115518812057/2500000000000 : ℚ) : ℝ) ≤ stT132 150 := by
  have hc : ((-141481/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115518812057/2500000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-141481/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c151 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-995751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95293/125000) (δ := 1331/200000000) (ψ := -502893/1000000) 132 105
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t151 : ((-810371899989/10000000000000 : ℚ) : ℝ) ≤ stT132 151 := by
  have hc : ((-995801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810371899989/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-995801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c152 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-711563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1476573/2500000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t152 : ((-144298749301/2500000000000 : ℚ) : ℝ) ≤ stT132 152 := by
  have hc : ((-711613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144298749301/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-711613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c153 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((73789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74847/200000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t153 : ((14903610507/2500000000000 : ℚ) : ℝ) ≤ stT132 153 := by
  have hc : ((73739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14903610507/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((73739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c154 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((200971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592499/10000000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t154 : ((161936780387/2500000000000 : ℚ) : ℝ) ≤ stT132 154 := by
  have hc : ((401917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161936780387/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((401917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c155 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((244117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271713/5000000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t155 : ((392138744771/5000000000000 : ℚ) : ℝ) ≤ stT132 155 := by
  have hc : ((488209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392138744771/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((488209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c156 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((483411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2665623/10000000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t156 : ((604684611/15625000000 : ℚ) : ℝ) ≤ stT132 156 := by
  have hc : ((483361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((604684611/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((483361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c157 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-41557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4774257/10000000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t157 : ((-132684358011/5000000000000 : ℚ) : ℝ) ≤ stT132 157 := by
  have hc : ((-166253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132684358011/5000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-166253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c158 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-923459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6869493/10000000) (δ := 6763/1000000000) (ψ := -502893/1000000) 132 106
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t158 : ((-367352486511/5000000000000 : ℚ) : ℝ) ≤ stT132 158 := by
  have hc : ((-923509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367352486511/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-923509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c159 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-905169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1351287/2000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t159 : ((-179471434597/2500000000000 : ℚ) : ℝ) ≤ stT132 159 := by
  have hc : ((-905219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179471434597/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-905219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c160 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-299521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4687467/10000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t160 : ((-23683184547/1000000000000 : ℚ) : ℝ) ≤ stT132 160 := by
  have hc : ((-299571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23683184547/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-299571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c161 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((123837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1315701/5000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t161 : ((19517465339/500000000000 : ℚ) : ℝ) ≤ stT132 161 := by
  have hc : ((247649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19517465339/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((247649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c162 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((60779/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294021/5000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t162 : ((191000099259/2500000000000 : ℚ) : ℝ) ≤ stT132 162 := by
  have hc : ((486207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191000099259/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((486207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c163 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((838049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288549/2000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t163 : ((32818554837/500000000000 : ℚ) : ℝ) ≤ stT132 163 := by
  have hc : ((837999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32818554837/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((837999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c164 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((185283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3461091/10000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t164 : ((36160630561/2500000000000 : ℚ) : ℝ) ≤ stT132 164 := by
  have hc : ((185233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36160630561/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((185233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c165 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-577831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5467161/10000000) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t165 : ((-449879780619/10000000000000 : ℚ) : ℝ) ≤ stT132 165 := by
  have hc : ((-577881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-449879780619/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-577881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c166 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-493839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11658/15625) (δ := 6733/1000000000) (ψ := -502893/1000000) 132 107
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t166 : ((-47914129683/625000000000 : ℚ) : ℝ) ≤ stT132 166 := by
  have hc : ((-61733/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47914129683/625000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-61733/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c167 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-20117/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626483/1000000) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t167 : ((-972999043/15625000000 : ℚ) : ℝ) ≤ stT132 167 := by
  have hc : ((-80473/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-972999043/15625000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-80473/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c168 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-146553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4294697/10000000) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t168 : ((-113106706751/10000000000000 : ℚ) : ℝ) ≤ stT132 168 := by
  have hc : ((-146603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113106706751/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-146603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c169 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((594233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2336213/10000000) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t169 : ((45706338909/1000000000000 : ℚ) : ℝ) ≤ stT132 169 := by
  have hc : ((594183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45706338909/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((594183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c170 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((987899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6083/156250) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t170 : ((189411155109/2500000000000 : ℚ) : ℝ) ≤ stT132 170 := by
  have hc : ((987849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189411155109/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((987849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c171 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((814767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1546171/10000000) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t171 : ((623029569523/10000000000000 : ℚ) : ℝ) ≤ stT132 171 := by
  have hc : ((814717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((623029569523/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((814717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c172 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((36327/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108449/312500) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t172 : ((6922855491/500000000000 : ℚ) : ℝ) ≤ stT132 172 := by
  have hc : ((36317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6922855491/500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((36317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c173 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-55017/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5383411/10000000) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t173 : ((-10458114073/250000000000 : ℚ) : ℝ) ≤ stT132 173 := by
  have hc : ((-27511/50000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10458114073/250000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-27511/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c174 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-974251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910679/1250000) (δ := 3313/500000000) (ψ := -502893/1000000) 132 108
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t174 : ((-738616613799/10000000000000 : ℚ) : ℝ) ≤ stT132 174 := by
  have hc : ((-974301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-738616613799/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-974301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c175 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-13489/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32657/50000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t175 : ((-326314139217/5000000000000 : ℚ) : ℝ) ≤ stT132 175 := by
  have hc : ((-431673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326314139217/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-431673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c176 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-57119/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232553/500000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t176 : ((-43062640491/2000000000000 : ℚ) : ℝ) ≤ stT132 176 := by
  have hc : ((-57129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43062640491/2000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-57129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c177 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((221193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1390673/5000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t177 : ((5195001329/156250000000 : ℚ) : ℝ) ≤ stT132 177 := by
  have hc : ((13823/31250 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5195001329/156250000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((13823/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c178 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((932733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57637/625000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t178 : ((699074821673/10000000000000 : ℚ) : ℝ) ≤ stT132 178 := by
  have hc : ((932683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699074821673/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((932683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c179 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((932101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926567/10000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t179 : ((139329507837/2000000000000 : ℚ) : ℝ) ≤ stT132 179 := by
  have hc : ((932051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139329507837/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((932051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c180 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((224121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2764997/10000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t180 : ((1043944213/31250000000 : ℚ) : ℝ) ≤ stT132 180 := by
  have hc : ((7003/15625 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1043944213/31250000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((7003/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c181 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-52673/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4593263/10000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t181 : ((-7831802097/400000000000 : ℚ) : ℝ) ≤ stT132 181 := by
  have hc : ((-52683/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7831802097/400000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-52683/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c182 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-209523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6411431/10000000) (δ := 1671/250000000) (ψ := -502893/1000000) 132 109
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t182 : ((-248509103/4000000000 : ℚ) : ℝ) ≤ stT132 182 := by
  have hc : ((-419071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248509103/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-419071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c183 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-989321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7488297/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t183 : ((-365682404681/5000000000000 : ℚ) : ℝ) ≤ stT132 183 := by
  have hc : ((-989371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365682404681/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-989371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c184 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-648167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5689929/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t184 : ((-47787205457/1000000000000 : ℚ) : ℝ) ≤ stT132 184 := by
  have hc : ((-648217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47787205457/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-648217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c185 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((5139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243831/625000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t185 : ((939971099/1250000000000 : ℚ) : ℝ) ≤ stT132 185 := by
  have hc : ((2557/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((939971099/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((2557/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c186 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((132157/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -530583/2500000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t186 : ((19378961109/400000000000 : ℚ) : ℝ) ≤ stT132 186 := by
  have hc : ((132147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19378961109/400000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((132147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c187 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((198011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44109/1250000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t187 : ((18099073409/250000000000 : ℚ) : ℝ) ≤ stT132 187 := by
  have hc : ((198001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18099073409/250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((198001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c188 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((845739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1407117/10000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t188 : ((154195321059/2500000000000 : ℚ) : ℝ) ≤ stT132 188 := by
  have hc : ((845689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154195321059/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((845689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c189 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((60569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15789/50000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t189 : ((1376566629/62500000000 : ℚ) : ℝ) ≤ stT132 189 := by
  have hc : ((60559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1376566629/62500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((60559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c190 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-379159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489921/1000000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t190 : ((-275107407693/10000000000000 : ℚ) : ℝ) ≤ stT132 190 := by
  have hc : ((-379209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275107407693/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-379209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c191 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-882809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 828939/1250000) (δ := 6791/1000000000) (ψ := -502893/1000000) 132 110
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t191 : ((-25552588037/400000000000 : ℚ) : ℝ) ≤ stT132 191 := by
  have hc : ((-882859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25552588037/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-882859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c192 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-490003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294129/400000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t192 : ((-11051478977/156250000000 : ℚ) : ℝ) ≤ stT132 192 := by
  have hc : ((-122507/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11051478977/156250000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-122507/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c193 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-632503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5638941/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t193 : ((-56915221281/1250000000000 : ℚ) : ℝ) ≤ stT132 193 := by
  have hc : ((-632553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56915221281/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-632553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c194 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-651/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3933501/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t194 : ((-952731593/5000000000000 : ℚ) : ℝ) ≤ stT132 194 := by
  have hc : ((-1327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-952731593/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-1327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c195 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((25029/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2236839/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t195 : ((8961092539/200000000000 : ℚ) : ℝ) ≤ stT132 195 := by
  have hc : ((25027/40000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8961092539/200000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((25027/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c196 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((975997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68607/1250000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t196 : ((139420860579/2000000000000 : ℚ) : ℝ) ≤ stT132 196 := by
  have hc : ((975947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139420860579/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((975947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c197 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((22487/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1130547/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t197 : ((6408168921/100000000000 : ℚ) : ℝ) ≤ stT132 197 := by
  have hc : ((89943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6408168921/100000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((89943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c198 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((87033/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 700359/2500000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t198 : ((61844548387/2000000000000 : ℚ) : ℝ) ≤ stT132 198 := by
  have hc : ((87023/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61844548387/2000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((87023/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c199 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-666/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 446391/1000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t199 : ((-7555618797/500000000000 : ℚ) : ℝ) ≤ stT132 199 := by
  have hc : ((-21317/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7555618797/500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-21317/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c200 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-768451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223607/2000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t200 : ((-543412436607/10000000000000 : ℚ) : ℝ) ≤ stT132 200 := by
  have hc : ((-768501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543412436607/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-768501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c201 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-124919/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7763943/10000000) (δ := 1341/200000000) (ψ := -502893/1000000) 132 111
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t201 : ((-176231050773/2500000000000 : ℚ) : ℝ) ≤ stT132 201 := by
  have hc : ((-499701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176231050773/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-499701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c202 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-101803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6306329/10000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t202 : ((-143265569363/2500000000000 : ℚ) : ℝ) ≤ stT132 202 := by
  have hc : ((-407237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143265569363/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-407237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c203 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-59081/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467669/1000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t203 : ((-41473786533/2000000000000 : ℚ) : ℝ) ≤ stT132 203 := by
  have hc : ((-59091/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41473786533/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-59091/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c204 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((341741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305507/1000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t204 : ((11961576837/500000000000 : ℚ) : ℝ) ≤ stT132 204 := by
  have hc : ((341691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11961576837/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((341691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c205 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((838349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144137/1000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t205 : ((58549317057/1000000000000 : ℚ) : ℝ) ≤ stT132 205 := by
  have hc : ((838299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58549317057/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((838299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c206 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((997837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41119/2500000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t206 : ((695191129871/10000000000000 : ℚ) : ℝ) ≤ stT132 206 := by
  have hc : ((997787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((695191129871/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((997787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c207 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((761603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881267/5000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t207 : ((66164486193/1250000000000 : ℚ) : ℝ) ≤ stT132 207 := by
  have hc : ((761553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66164486193/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((761553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c208 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((113811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3352903/10000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t208 : ((315585471/20000000000 : ℚ) : ℝ) ≤ stT132 208 := by
  have hc : ((56893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315585471/20000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((56893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c209 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-196303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4935649/10000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t209 : ((-3395075563/125000000000 : ℚ) : ℝ) ≤ stT132 209 := by
  have hc : ((-24541/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3395075563/125000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-24541/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c210 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-171823/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3255419/5000000) (δ := 3303/500000000) (ψ := -502893/1000000) 132 112
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t210 : ((-59288055489/1000000000000 : ℚ) : ℝ) ≤ stT132 210 := by
  have hc : ((-171833/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59288055489/1000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-171833/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c211 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-995969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7629427/10000000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t211 : ((-685688364151/10000000000000 : ℚ) : ℝ) ≤ stT132 211 := by
  have hc : ((-996019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685688364151/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-996019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c212 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-377897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3034577/5000000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t212 : ((-129778981683/2500000000000 : ℚ) : ℝ) ≤ stT132 212 := by
  have hc : ((-188961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129778981683/2500000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-188961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c213 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-233511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4516207/10000000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t213 : ((-160033428029/10000000000000 : ℚ) : ℝ) ≤ stT132 213 := by
  have hc : ((-233561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160033428029/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-233561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c214 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((373323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74263/250000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t214 : ((51032764741/2000000000000 : ℚ) : ℝ) ≤ stT132 214 := by
  have hc : ((373273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51032764741/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((373273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c215 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((420187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71603/500000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t215 : ((71636990757/1250000000000 : ℚ) : ℝ) ≤ stT132 215 := by
  have hc : ((210081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71636990757/1250000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((210081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c216 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((249803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12409/1250000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t216 : ((339921406953/5000000000000 : ℚ) : ℝ) ≤ stT132 216 := by
  have hc : ((499581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339921406953/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((499581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c217 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((159289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1623509/10000000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t217 : ((27031398369/500000000000 : ℚ) : ℝ) ≤ stT132 217 := by
  have hc : ((159279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27031398369/500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((159279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c218 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((154669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12563/40000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t218 : ((5236903077/250000000000 : ℚ) : ℝ) ≤ stT132 218 := by
  have hc : ((38661/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5236903077/250000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((38661/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c219 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-71399/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4651061/10000000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t219 : ((-48255464187/2500000000000 : ℚ) : ℝ) ≤ stT132 219 := by
  have hc : ((-142823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48255464187/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-142823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c220 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-777697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246179/400000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t220 : ((-2621785137/50000000000 : ℚ) : ℝ) ≤ stT132 220 := by
  have hc : ((-777747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2621785137/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-777747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c221 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-996709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7651091/10000000) (δ := 6713/1000000000) (ψ := -502893/1000000) 132 113
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t221 : ((-670492866807/10000000000000 : ℚ) : ℝ) ≤ stT132 221 := by
  have hc : ((-996759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-670492866807/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-996759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c222 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-435203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1313411/2000000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t222 : ((-73026579699/1250000000000 : ℚ) : ℝ) ≤ stT132 222 := by
  have hc : ((-108807/125000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73026579699/1250000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-108807/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c223 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-55803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5083903/10000000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t223 : ((-2989813141/100000000000 : ℚ) : ℝ) ≤ stT132 223 := by
  have hc : ((-223237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2989813141/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-223237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c224 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((25499/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450923/1250000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t224 : ((17030551817/2000000000000 : ℚ) : ℝ) ≤ stT132 224 := by
  have hc : ((25489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17030551817/2000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((25489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c225 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((656239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267179/1250000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t225 : ((218729447937/5000000000000 : ℚ) : ℝ) ≤ stT132 225 := by
  have hc : ((656189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218729447937/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((656189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c226 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((481937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67403/1000000) (δ := 661/50000000) (ψ := -502893/1000000) 132 114
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t226 : ((4007038041/62500000000 : ℚ) : ℝ) ≤ stT132 226 := by
  have hc : ((60239/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4007038041/62500000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((60239/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c227 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((2973/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97867/1250000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t227 : ((63140632713/1000000000000 : ℚ) : ℝ) ≤ stT132 227 := by
  have hc : ((95131/100000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63140632713/1000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((95131/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c228 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((626771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 558371/2500000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t228 : ((207528004893/5000000000000 : ℚ) : ℝ) ≤ stT132 228 := by
  have hc : ((626721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207528004893/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((626721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c229 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((99553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28732/78125) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t229 : ((32876686727/5000000000000 : ℚ) : ℝ) ≤ stT132 229 := by
  have hc : ((99503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32876686727/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((99503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c230 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-91547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1023121/2000000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t230 : ((-60370946217/2000000000000 : ℚ) : ℝ) ≤ stT132 230 := by
  have hc : ((-91557/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60370946217/2000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-91557/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c231 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-216621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6547277/10000000) (δ := 6783/1000000000) (ψ := -502893/1000000) 132 114
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t231 : ((-8908402787/156250000000 : ℚ) : ℝ) ≤ stT132 231 := by
  have hc : ((-433267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8908402787/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-433267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c232 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-124859/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3867609/5000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t232 : ((-327912628713/5000000000000 : ℚ) : ℝ) ≤ stT132 232 := by
  have hc : ((-499461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327912628713/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-499461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c233 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-816629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263171/2000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t233 : ((-267512189919/5000000000000 : ℚ) : ℝ) ≤ stT132 233 := by
  have hc : ((-816679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267512189919/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-816679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c234 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-951/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225641/2500000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t234 : ((-4974163089/200000000000 : ℚ) : ℝ) ≤ stT132 234 := by
  have hc : ((-7609/20000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4974163089/200000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-7609/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c235 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((34363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218457/625000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t235 : ((2801177973/250000000000 : ℚ) : ℝ) ≤ stT132 235 := by
  have hc : ((34353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2801177973/250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((34353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c236 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((334619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2094033/10000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t236 : ((1701577787/39062500000 : ℚ) : ℝ) ≤ stT132 236 := by
  have hc : ((167297/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1701577787/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((167297/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c237 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((2403/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349347/5000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t237 : ((12486664887/200000000000 : ℚ) : ℝ) ≤ stT132 237 := by
  have hc : ((19223/20000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12486664887/200000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((19223/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c238 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((962069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 690771/10000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t238 : ((623583601857/10000000000000 : ℚ) : ℝ) ≤ stT132 238 := by
  have hc : ((962019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((623583601857/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((962019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c239 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((135009/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518607/2500000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t239 : ((43661781577/1000000000000 : ℚ) : ℝ) ≤ stT132 239 := by
  have hc : ((134999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43661781577/1000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((134999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c240 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((94367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 345231/1000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t240 : ((30448738987/2500000000000 : ℚ) : ℝ) ≤ stT132 240 := by
  have hc : ((47171/250000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30448738987/2500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((47171/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c241 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-351323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96489/200000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t241 : ((-226339377561/10000000000000 : ℚ) : ℝ) ≤ stT132 241 := by
  have hc : ((-351373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226339377561/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-351373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c242 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-786777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3095457/5000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t242 : ((-20231682651/400000000000 : ℚ) : ℝ) ≤ stT132 242 := by
  have hc : ((-786827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20231682651/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-786827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c243 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-992701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510347/2000000) (δ := 1669/250000000) (ψ := -502893/1000000) 132 115
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t243 : ((-636850759251/10000000000000 : ℚ) : ℝ) ≤ stT132 243 := by
  have hc : ((-992751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-636850759251/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-992751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c244 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-912599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -850123/1250000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t244 : ((-116852840013/2000000000000 : ℚ) : ℝ) ≤ stT132 244 := by
  have hc : ((-912649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116852840013/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-912649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c245 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-572641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5451301/10000000) (δ := 13369/1000000000) (ψ := -502893/1000000) 132 116
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t245 : ((-365879108007/10000000000000 : ℚ) : ℝ) ≤ stT132 245 := by
  have hc : ((-572691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365879108007/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-572691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c246 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((-71979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -821419/2000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t246 : ((-45924033733/10000000000000 : ℚ) : ℝ) ≤ stT132 246 := by
  have hc : ((-72029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45924033733/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-72029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c247 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((223521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2768351/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t247 : ((4443966527/156250000000 : ℚ) : ℝ) ≤ stT132 247 := by
  have hc : ((27937/62500 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4443966527/156250000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((27937/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c248 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((209933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1435019/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t248 : ((53319807/1000000000 : ℚ) : ℝ) ≤ stT132 248 := by
  have hc : ((419841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53319807/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((419841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c249 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((999083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53533/5000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t249 : ((158277797223/2500000000000 : ℚ) : ℝ) ≤ stT132 249 := by
  have hc : ((999033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158277797223/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((999033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_c250 :
    |Real.cos (((132 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((176819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1215607/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st132_t250 : ((22364747219/400000000000 : ℚ) : ℝ) ≤ stT132 250 := by
  have hc : ((176809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((132 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st132_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22364747219/400000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((176809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st132_p1 : ((438071/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT132 (i+1) := by
  rw [Finset.sum_range_one]
  exact st132_t1

theorem st132_p2 : ((540270135399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT132 (i+1))
      = (∑ i ∈ Finset.range 1, stT132 (i+1)) + stT132 2 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 1
    simpa using h
  have hprev := st132_p1
  have hstep := st132_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p3 : ((3704958277661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT132 (i+1))
      = (∑ i ∈ Finset.range 2, stT132 (i+1)) + stT132 3 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 2
    simpa using h
  have hprev := st132_p2
  have hstep := st132_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p4 : ((4418330777661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT132 (i+1))
      = (∑ i ∈ Finset.range 3, stT132 (i+1)) + stT132 4 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 3
    simpa using h
  have hprev := st132_p3
  have hstep := st132_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p5 : ((12314976354947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT132 (i+1))
      = (∑ i ∈ Finset.range 4, stT132 (i+1)) + stT132 5 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 4
    simpa using h
  have hprev := st132_p4
  have hstep := st132_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p6 : ((2900889696221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT132 (i+1))
      = (∑ i ∈ Finset.range 5, stT132 (i+1)) + stT132 6 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 5
    simpa using h
  have hprev := st132_p5
  have hstep := st132_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p7 : ((3816945004103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT132 (i+1))
      = (∑ i ∈ Finset.range 6, stT132 (i+1)) + stT132 7 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 6
    simpa using h
  have hprev := st132_p6
  have hstep := st132_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p8 : ((15619936780877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT132 (i+1))
      = (∑ i ∈ Finset.range 7, stT132 (i+1)) + stT132 8 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 7
    simpa using h
  have hprev := st132_p7
  have hstep := st132_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p9 : ((3955566690161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT132 (i+1))
      = (∑ i ∈ Finset.range 8, stT132 (i+1)) + stT132 9 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 8
    simpa using h
  have hprev := st132_p8
  have hstep := st132_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p10 : ((6396103383051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT132 (i+1))
      = (∑ i ∈ Finset.range 9, stT132 (i+1)) + stT132 10 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 9
    simpa using h
  have hprev := st132_p9
  have hstep := st132_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p11 : ((4945441584231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT132 (i+1))
      = (∑ i ∈ Finset.range 10, stT132 (i+1)) + stT132 11 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 10
    simpa using h
  have hprev := st132_p10
  have hstep := st132_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p12 : ((185545734207/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT132 (i+1))
      = (∑ i ∈ Finset.range 11, stT132 (i+1)) + stT132 12 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 11
    simpa using h
  have hprev := st132_p11
  have hstep := st132_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p13 : ((239726389527/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT132 (i+1))
      = (∑ i ∈ Finset.range 12, stT132 (i+1)) + stT132 13 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 12
    simpa using h
  have hprev := st132_p12
  have hstep := st132_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p14 : ((233508810699/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT132 (i+1))
      = (∑ i ∈ Finset.range 13, stT132 (i+1)) + stT132 14 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 13
    simpa using h
  have hprev := st132_p13
  have hstep := st132_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p15 : ((1485288660751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT132 (i+1))
      = (∑ i ∈ Finset.range 14, stT132 (i+1)) + stT132 15 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 14
    simpa using h
  have hprev := st132_p14
  have hstep := st132_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p16 : ((5353841908079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT132 (i+1))
      = (∑ i ∈ Finset.range 15, stT132 (i+1)) + stT132 16 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 15
    simpa using h
  have hprev := st132_p15
  have hstep := st132_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p17 : ((350344833967/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT132 (i+1))
      = (∑ i ∈ Finset.range 16, stT132 (i+1)) + stT132 17 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 16
    simpa using h
  have hprev := st132_p16
  have hstep := st132_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p18 : ((9518838225901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT132 (i+1))
      = (∑ i ∈ Finset.range 17, stT132 (i+1)) + stT132 18 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 17
    simpa using h
  have hprev := st132_p17
  have hstep := st132_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p19 : ((11641782288991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT132 (i+1))
      = (∑ i ∈ Finset.range 18, stT132 (i+1)) + stT132 19 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 18
    simpa using h
  have hprev := st132_p18
  have hstep := st132_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p20 : ((13866816534413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT132 (i+1))
      = (∑ i ∈ Finset.range 19, stT132 (i+1)) + stT132 20 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 19
    simpa using h
  have hprev := st132_p19
  have hstep := st132_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p21 : ((15977770426671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT132 (i+1))
      = (∑ i ∈ Finset.range 20, stT132 (i+1)) + stT132 21 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 20
    simpa using h
  have hprev := st132_p20
  have hstep := st132_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p22 : ((9047982076659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT132 (i+1))
      = (∑ i ∈ Finset.range 21, stT132 (i+1)) + stT132 22 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 21
    simpa using h
  have hprev := st132_p21
  have hstep := st132_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p23 : ((10043289075039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT132 (i+1))
      = (∑ i ∈ Finset.range 22, stT132 (i+1)) + stT132 23 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 22
    simpa using h
  have hprev := st132_p22
  have hstep := st132_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p24 : ((10622368734329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT132 (i+1))
      = (∑ i ∈ Finset.range 23, stT132 (i+1)) + stT132 24 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 23
    simpa using h
  have hprev := st132_p23
  have hstep := st132_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p25 : ((20670243181411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT132 (i+1))
      = (∑ i ∈ Finset.range 24, stT132 (i+1)) + stT132 25 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 24
    simpa using h
  have hprev := st132_p24
  have hstep := st132_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p26 : ((18738408397959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT132 (i+1))
      = (∑ i ∈ Finset.range 25, stT132 (i+1)) + stT132 26 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 25
    simpa using h
  have hprev := st132_p25
  have hstep := st132_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p27 : ((17913763568461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT132 (i+1))
      = (∑ i ∈ Finset.range 26, stT132 (i+1)) + stT132 27 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 26
    simpa using h
  have hprev := st132_p26
  have hstep := st132_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p28 : ((19543340070663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT132 (i+1))
      = (∑ i ∈ Finset.range 27, stT132 (i+1)) + stT132 28 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 27
    simpa using h
  have hprev := st132_p27
  have hstep := st132_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p29 : ((20351935398889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT132 (i+1))
      = (∑ i ∈ Finset.range 28, stT132 (i+1)) + stT132 29 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 28
    simpa using h
  have hprev := st132_p28
  have hstep := st132_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p30 : ((18567436910669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT132 (i+1))
      = (∑ i ∈ Finset.range 29, stT132 (i+1)) + stT132 30 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 29
    simpa using h
  have hprev := st132_p29
  have hstep := st132_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p31 : ((471821258379/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT132 (i+1))
      = (∑ i ∈ Finset.range 30, stT132 (i+1)) + stT132 31 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 30
    simpa using h
  have hprev := st132_p30
  have hstep := st132_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p32 : ((10116669479327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT132 (i+1))
      = (∑ i ∈ Finset.range 31, stT132 (i+1)) + stT132 32 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 31
    simpa using h
  have hprev := st132_p31
  have hstep := st132_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p33 : ((14482371647/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT132 (i+1))
      = (∑ i ∈ Finset.range 32, stT132 (i+1)) + stT132 33 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 32
    simpa using h
  have hprev := st132_p32
  have hstep := st132_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p34 : ((3884999408033/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT132 (i+1))
      = (∑ i ∈ Finset.range 33, stT132 (i+1)) + stT132 34 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 33
    simpa using h
  have hprev := st132_p33
  have hstep := st132_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p35 : ((786480481117/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT132 (i+1))
      = (∑ i ∈ Finset.range 34, stT132 (i+1)) + stT132 35 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 34
    simpa using h
  have hprev := st132_p34
  have hstep := st132_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p36 : ((18565838475357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT132 (i+1))
      = (∑ i ∈ Finset.range 35, stT132 (i+1)) + stT132 36 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 35
    simpa using h
  have hprev := st132_p35
  have hstep := st132_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p37 : ((1004683736027/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT132 (i+1))
      = (∑ i ∈ Finset.range 36, stT132 (i+1)) + stT132 37 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 36
    simpa using h
  have hprev := st132_p36
  have hstep := st132_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p38 : ((1847137860979/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT132 (i+1))
      = (∑ i ∈ Finset.range 37, stT132 (i+1)) + stT132 38 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 37
    simpa using h
  have hprev := st132_p37
  have hstep := st132_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p39 : ((20006736472301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT132 (i+1))
      = (∑ i ∈ Finset.range 38, stT132 (i+1)) + stT132 39 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 38
    simpa using h
  have hprev := st132_p38
  have hstep := st132_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p40 : ((4652542142797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT132 (i+1))
      = (∑ i ∈ Finset.range 39, stT132 (i+1)) + stT132 40 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 39
    simpa using h
  have hprev := st132_p39
  have hstep := st132_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p41 : ((4973444738083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT132 (i+1))
      = (∑ i ∈ Finset.range 40, stT132 (i+1)) + stT132 41 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 40
    simpa using h
  have hprev := st132_p40
  have hstep := st132_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p42 : ((9330443535581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT132 (i+1))
      = (∑ i ∈ Finset.range 41, stT132 (i+1)) + stT132 42 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 41
    simpa using h
  have hprev := st132_p41
  have hstep := st132_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p43 : ((19911046899387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT132 (i+1))
      = (∑ i ∈ Finset.range 42, stT132 (i+1)) + stT132 43 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 42
    simpa using h
  have hprev := st132_p42
  have hstep := st132_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p44 : ((9294959460339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT132 (i+1))
      = (∑ i ∈ Finset.range 43, stT132 (i+1)) + stT132 44 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 43
    simpa using h
  have hprev := st132_p43
  have hstep := st132_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p45 : ((10000659066317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT132 (i+1))
      = (∑ i ∈ Finset.range 44, stT132 (i+1)) + stT132 45 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 44
    simpa using h
  have hprev := st132_p44
  have hstep := st132_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p46 : ((9266209180557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT132 (i+1))
      = (∑ i ∈ Finset.range 45, stT132 (i+1)) + stT132 46 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 45
    simpa using h
  have hprev := st132_p45
  have hstep := st132_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p47 : ((9978607517561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT132 (i+1))
      = (∑ i ∈ Finset.range 46, stT132 (i+1)) + stT132 47 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 46
    simpa using h
  have hprev := st132_p46
  have hstep := st132_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p48 : ((9374183713929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT132 (i+1))
      = (∑ i ∈ Finset.range 47, stT132 (i+1)) + stT132 48 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 47
    simpa using h
  have hprev := st132_p47
  have hstep := st132_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p49 : ((4880631084617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT132 (i+1))
      = (∑ i ∈ Finset.range 48, stT132 (i+1)) + stT132 49 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 48
    simpa using h
  have hprev := st132_p48
  have hstep := st132_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p50 : ((1211510029321/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT132 (i+1))
      = (∑ i ∈ Finset.range 49, stT132 (i+1)) + stT132 50 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 49
    simpa using h
  have hprev := st132_p49
  have hstep := st132_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p51 : ((18800729189643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT132 (i+1))
      = (∑ i ∈ Finset.range 50, stT132 (i+1)) + stT132 51 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 50
    simpa using h
  have hprev := st132_p50
  have hstep := st132_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p52 : ((19973606284143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT132 (i+1))
      = (∑ i ∈ Finset.range 51, stT132 (i+1)) + stT132 52 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 51
    simpa using h
  have hprev := st132_p51
  have hstep := st132_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p53 : ((3720558290307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT132 (i+1))
      = (∑ i ∈ Finset.range 52, stT132 (i+1)) + stT132 53 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 52
    simpa using h
  have hprev := st132_p52
  have hstep := st132_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p54 : ((19608771924669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT132 (i+1))
      = (∑ i ∈ Finset.range 53, stT132 (i+1)) + stT132 54 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 53
    simpa using h
  have hprev := st132_p53
  have hstep := st132_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p55 : ((19457320985069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT132 (i+1))
      = (∑ i ∈ Finset.range 54, stT132 (i+1)) + stT132 55 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 54
    simpa using h
  have hprev := st132_p54
  have hstep := st132_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p56 : ((9323927178063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT132 (i+1))
      = (∑ i ∈ Finset.range 55, stT132 (i+1)) + stT132 56 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 55
    simpa using h
  have hprev := st132_p55
  have hstep := st132_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p57 : ((9981792420493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT132 (i+1))
      = (∑ i ∈ Finset.range 56, stT132 (i+1)) + stT132 57 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 56
    simpa using h
  have hprev := st132_p56
  have hstep := st132_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p58 : ((2373238191177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT132 (i+1))
      = (∑ i ∈ Finset.range 57, stT132 (i+1)) + stT132 58 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 57
    simpa using h
  have hprev := st132_p57
  have hstep := st132_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p59 : ((4731720110149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT132 (i+1))
      = (∑ i ∈ Finset.range 58, stT132 (i+1)) + stT132 59 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 58
    simpa using h
  have hprev := st132_p58
  have hstep := st132_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p60 : ((9995269717077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT132 (i+1))
      = (∑ i ∈ Finset.range 59, stT132 (i+1)) + stT132 60 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 59
    simpa using h
  have hprev := st132_p59
  have hstep := st132_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p61 : ((18790962998423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT132 (i+1))
      = (∑ i ∈ Finset.range 60, stT132 (i+1)) + stT132 61 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 60
    simpa using h
  have hprev := st132_p60
  have hstep := st132_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p62 : ((3813189230989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT132 (i+1))
      = (∑ i ∈ Finset.range 61, stT132 (i+1)) + stT132 62 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 61
    simpa using h
  have hprev := st132_p61
  have hstep := st132_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p63 : ((3995894653847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT132 (i+1))
      = (∑ i ∈ Finset.range 62, stT132 (i+1)) + stT132 63 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 62
    simpa using h
  have hprev := st132_p62
  have hstep := st132_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p64 : ((18786449814817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT132 (i+1))
      = (∑ i ∈ Finset.range 63, stT132 (i+1)) + stT132 64 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 63
    simpa using h
  have hprev := st132_p63
  have hstep := st132_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p65 : ((9499643579141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT132 (i+1))
      = (∑ i ∈ Finset.range 64, stT132 (i+1)) + stT132 65 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 64
    simpa using h
  have hprev := st132_p64
  have hstep := st132_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p66 : ((10001585690061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT132 (i+1))
      = (∑ i ∈ Finset.range 65, stT132 (i+1)) + stT132 66 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 65
    simpa using h
  have hprev := st132_p65
  have hstep := st132_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p67 : ((9477493195401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT132 (i+1))
      = (∑ i ∈ Finset.range 66, stT132 (i+1)) + stT132 67 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 66
    simpa using h
  have hprev := st132_p66
  have hstep := st132_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p68 : ((750719020967/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT132 (i+1))
      = (∑ i ∈ Finset.range 67, stT132 (i+1)) + stT132 68 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 67
    simpa using h
  have hprev := st132_p67
  have hstep := st132_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p69 : ((19947424099367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT132 (i+1))
      = (∑ i ∈ Finset.range 68, stT132 (i+1)) + stT132 69 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 68
    simpa using h
  have hprev := st132_p68
  have hstep := st132_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p70 : ((19343159345211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT132 (i+1))
      = (∑ i ∈ Finset.range 69, stT132 (i+1)) + stT132 70 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 69
    simpa using h
  have hprev := st132_p69
  have hstep := st132_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p71 : ((18543526995687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT132 (i+1))
      = (∑ i ∈ Finset.range 70, stT132 (i+1)) + stT132 71 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 70
    simpa using h
  have hprev := st132_p70
  have hstep := st132_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p72 : ((9798725852661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT132 (i+1))
      = (∑ i ∈ Finset.range 71, stT132 (i+1)) + stT132 72 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 71
    simpa using h
  have hprev := st132_p71
  have hstep := st132_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p73 : ((19845877292127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT132 (i+1))
      = (∑ i ∈ Finset.range 72, stT132 (i+1)) + stT132 73 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 72
    simpa using h
  have hprev := st132_p72
  have hstep := st132_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p74 : ((2335426925541/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT132 (i+1))
      = (∑ i ∈ Finset.range 73, stT132 (i+1)) + stT132 74 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 73
    simpa using h
  have hprev := st132_p73
  have hstep := st132_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p75 : ((1182913789233/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT132 (i+1))
      = (∑ i ∈ Finset.range 74, stT132 (i+1)) + stT132 75 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 74
    simpa using h
  have hprev := st132_p74
  have hstep := st132_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p76 : ((9993789726361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT132 (i+1))
      = (∑ i ∈ Finset.range 75, stT132 (i+1)) + stT132 76 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 75
    simpa using h
  have hprev := st132_p75
  have hstep := st132_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p77 : ((9698582769303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT132 (i+1))
      = (∑ i ∈ Finset.range 76, stT132 (i+1)) + stT132 77 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 76
    simpa using h
  have hprev := st132_p76
  have hstep := st132_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p78 : ((370291051461/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT132 (i+1))
      = (∑ i ∈ Finset.range 77, stT132 (i+1)) + stT132 78 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 77
    simpa using h
  have hprev := st132_p77
  have hstep := st132_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p79 : ((19311927606951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT132 (i+1))
      = (∑ i ∈ Finset.range 78, stT132 (i+1)) + stT132 79 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 78
    simpa using h
  have hprev := st132_p78
  have hstep := st132_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p80 : ((20026498274307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT132 (i+1))
      = (∑ i ∈ Finset.range 79, stT132 (i+1)) + stT132 80 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 79
    simpa using h
  have hprev := st132_p79
  have hstep := st132_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p81 : ((19125020886459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT132 (i+1))
      = (∑ i ∈ Finset.range 80, stT132 (i+1)) + stT132 81 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 80
    simpa using h
  have hprev := st132_p80
  have hstep := st132_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p82 : ((18523841194903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT132 (i+1))
      = (∑ i ∈ Finset.range 81, stT132 (i+1)) + stT132 82 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 81
    simpa using h
  have hprev := st132_p81
  have hstep := st132_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p83 : ((19461627004591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT132 (i+1))
      = (∑ i ∈ Finset.range 82, stT132 (i+1)) + stT132 83 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 82
    simpa using h
  have hprev := st132_p82
  have hstep := st132_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p84 : ((5004772912979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT132 (i+1))
      = (∑ i ∈ Finset.range 83, stT132 (i+1)) + stT132 84 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 83
    simpa using h
  have hprev := st132_p83
  have hstep := st132_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p85 : ((9545751457117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT132 (i+1))
      = (∑ i ∈ Finset.range 84, stT132 (i+1)) + stT132 85 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 84
    simpa using h
  have hprev := st132_p84
  have hstep := st132_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p86 : ((9253916002181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT132 (i+1))
      = (∑ i ∈ Finset.range 85, stT132 (i+1)) + stT132 86 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 85
    simpa using h
  have hprev := st132_p85
  have hstep := st132_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p87 : ((9691214405301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT132 (i+1))
      = (∑ i ∈ Finset.range 86, stT132 (i+1)) + stT132 87 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 86
    simpa using h
  have hprev := st132_p86
  have hstep := st132_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p88 : ((20051724124167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT132 (i+1))
      = (∑ i ∈ Finset.range 87, stT132 (i+1)) + stT132 88 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 87
    simpa using h
  have hprev := st132_p87
  have hstep := st132_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p89 : ((19281974776527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT132 (i+1))
      = (∑ i ∈ Finset.range 88, stT132 (i+1)) + stT132 89 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 88
    simpa using h
  have hprev := st132_p88
  have hstep := st132_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p90 : ((4621799535341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT132 (i+1))
      = (∑ i ∈ Finset.range 89, stT132 (i+1)) + stT132 90 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 89
    simpa using h
  have hprev := st132_p89
  have hstep := st132_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p91 : ((596342891623/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT132 (i+1))
      = (∑ i ∈ Finset.range 90, stT132 (i+1)) + stT132 91 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 90
    simpa using h
  have hprev := st132_p90
  have hstep := st132_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p92 : ((10004707261/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT132 (i+1))
      = (∑ i ∈ Finset.range 91, stT132 (i+1)) + stT132 92 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 91
    simpa using h
  have hprev := st132_p91
  have hstep := st132_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p93 : ((2458847008801/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT132 (i+1))
      = (∑ i ∈ Finset.range 92, stT132 (i+1)) + stT132 93 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 92
    simpa using h
  have hprev := st132_p92
  have hstep := st132_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p94 : ((1865480580339/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT132 (i+1))
      = (∑ i ∈ Finset.range 93, stT132 (i+1)) + stT132 94 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 93
    simpa using h
  have hprev := st132_p93
  have hstep := st132_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p95 : ((4663597313979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT132 (i+1))
      = (∑ i ∈ Finset.range 94, stT132 (i+1)) + stT132 95 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 94
    simpa using h
  have hprev := st132_p94
  have hstep := st132_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p96 : ((4914198817849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT132 (i+1))
      = (∑ i ∈ Finset.range 95, stT132 (i+1)) + stT132 96 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 95
    simpa using h
  have hprev := st132_p95
  have hstep := st132_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p97 : ((10022251047729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT132 (i+1))
      = (∑ i ∈ Finset.range 96, stT132 (i+1)) + stT132 97 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 96
    simpa using h
  have hprev := st132_p96
  have hstep := st132_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p98 : ((19215779645329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT132 (i+1))
      = (∑ i ∈ Finset.range 97, stT132 (i+1)) + stT132 98 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 97
    simpa using h
  have hprev := st132_p97
  have hstep := st132_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p99 : ((18467693680561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT132 (i+1))
      = (∑ i ∈ Finset.range 98, stT132 (i+1)) + stT132 99 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 98
    simpa using h
  have hprev := st132_p98
  have hstep := st132_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p100 : ((29587147207/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT132 (i+1))
      = (∑ i ∈ Finset.range 99, stT132 (i+1)) + stT132 100 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 99
    simpa using h
  have hprev := st132_p99
  have hstep := st132_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p101 : ((3980919392543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT132 (i+1))
      = (∑ i ∈ Finset.range 100, stT132 (i+1)) + stT132 101 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 100
    simpa using h
  have hprev := st132_p100
  have hstep := st132_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p102 : ((9972299945831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT132 (i+1))
      = (∑ i ∈ Finset.range 101, stT132 (i+1)) + stT132 102 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 101
    simpa using h
  have hprev := st132_p101
  have hstep := st132_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p103 : ((9505157948821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT132 (i+1))
      = (∑ i ∈ Finset.range 102, stT132 (i+1)) + stT132 103 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 102
    simpa using h
  have hprev := st132_p102
  have hstep := st132_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p104 : ((1844141025771/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT132 (i+1))
      = (∑ i ∈ Finset.range 103, stT132 (i+1)) + stT132 104 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 103
    simpa using h
  have hprev := st132_p103
  have hstep := st132_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p105 : ((1902752115921/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT132 (i+1))
      = (∑ i ∈ Finset.range 104, stT132 (i+1)) + stT132 105 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 104
    simpa using h
  have hprev := st132_p104
  have hstep := st132_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p106 : ((1994800795371/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT132 (i+1))
      = (∑ i ∈ Finset.range 105, stT132 (i+1)) + stT132 106 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 105
    simpa using h
  have hprev := st132_p105
  have hstep := st132_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p107 : ((1995439324499/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT132 (i+1))
      = (∑ i ∈ Finset.range 106, stT132 (i+1)) + stT132 107 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 106
    simpa using h
  have hprev := st132_p106
  have hstep := st132_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p108 : ((4762569881477/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT132 (i+1))
      = (∑ i ∈ Finset.range 107, stT132 (i+1)) + stT132 108 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 107
    simpa using h
  have hprev := st132_p107
  have hstep := st132_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p109 : ((460761167159/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT132 (i+1))
      = (∑ i ∈ Finset.range 108, stT132 (i+1)) + stT132 109 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 108
    simpa using h
  have hprev := st132_p108
  have hstep := st132_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p110 : ((9444488525121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT132 (i+1))
      = (∑ i ∈ Finset.range 109, stT132 (i+1)) + stT132 110 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 109
    simpa using h
  have hprev := st132_p109
  have hstep := st132_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p111 : ((9915308363401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT132 (i+1))
      = (∑ i ∈ Finset.range 110, stT132 (i+1)) + stT132 111 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 110
    simpa using h
  have hprev := st132_p110
  have hstep := st132_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p112 : ((10037383305313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT132 (i+1))
      = (∑ i ∈ Finset.range 111, stT132 (i+1)) + stT132 112 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 111
    simpa using h
  have hprev := st132_p111
  have hstep := st132_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p113 : ((19330894302039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT132 (i+1))
      = (∑ i ∈ Finset.range 112, stT132 (i+1)) + stT132 113 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 112
    simpa using h
  have hprev := st132_p112
  have hstep := st132_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p114 : ((18510786819929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT132 (i+1))
      = (∑ i ∈ Finset.range 113, stT132 (i+1)) + stT132 114 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 113
    simpa using h
  have hprev := st132_p113
  have hstep := st132_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p115 : ((18591025059113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT132 (i+1))
      = (∑ i ∈ Finset.range 114, stT132 (i+1)) + stT132 115 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 114
    simpa using h
  have hprev := st132_p114
  have hstep := st132_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p116 : ((19465764582137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT132 (i+1))
      = (∑ i ∈ Finset.range 115, stT132 (i+1)) + stT132 116 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 115
    simpa using h
  have hprev := st132_p115
  have hstep := st132_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p117 : ((20115553105137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT132 (i+1))
      = (∑ i ∈ Finset.range 116, stT132 (i+1)) + stT132 117 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 116
    simpa using h
  have hprev := st132_p116
  have hstep := st132_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p118 : ((9902545053481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT132 (i+1))
      = (∑ i ∈ Finset.range 117, stT132 (i+1)) + stT132 118 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 117
    simpa using h
  have hprev := st132_p117
  have hstep := st132_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p119 : ((9447092322321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT132 (i+1))
      = (∑ i ∈ Finset.range 118, stT132 (i+1)) + stT132 119 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 118
    simpa using h
  have hprev := st132_p118
  have hstep := st132_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p120 : ((2299317413591/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT132 (i+1))
      = (∑ i ∈ Finset.range 119, stT132 (i+1)) + stT132 120 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 119
    simpa using h
  have hprev := st132_p119
  have hstep := st132_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p121 : ((4710825169537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT132 (i+1))
      = (∑ i ∈ Finset.range 120, stT132 (i+1)) + stT132 121 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 120
    simpa using h
  have hprev := st132_p120
  have hstep := st132_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p122 : ((19748149772871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT132 (i+1))
      = (∑ i ∈ Finset.range 121, stT132 (i+1)) + stT132 122 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 121
    simpa using h
  have hprev := st132_p121
  have hstep := st132_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p123 : ((5037359164913/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT132 (i+1))
      = (∑ i ∈ Finset.range 122, stT132 (i+1)) + stT132 123 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 122
    simpa using h
  have hprev := st132_p122
  have hstep := st132_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p124 : ((4909187363311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT132 (i+1))
      = (∑ i ∈ Finset.range 123, stT132 (i+1)) + stT132 124 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 123
    simpa using h
  have hprev := st132_p123
  have hstep := st132_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p125 : ((1171655089867/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT132 (i+1))
      = (∑ i ∈ Finset.range 124, stT132 (i+1)) + stT132 125 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 124
    simpa using h
  have hprev := st132_p124
  have hstep := st132_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p126 : ((18381553059271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT132 (i+1))
      = (∑ i ∈ Finset.range 125, stT132 (i+1)) + stT132 126 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 125
    simpa using h
  have hprev := st132_p125
  have hstep := st132_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p127 : ((18898161074199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT132 (i+1))
      = (∑ i ∈ Finset.range 126, stT132 (i+1)) + stT132 127 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 126
    simpa using h
  have hprev := st132_p126
  have hstep := st132_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p128 : ((19778734816247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT132 (i+1))
      = (∑ i ∈ Finset.range 127, stT132 (i+1)) + stT132 128 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 127
    simpa using h
  have hprev := st132_p127
  have hstep := st132_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p129 : ((20167639266197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT132 (i+1))
      = (∑ i ∈ Finset.range 128, stT132 (i+1)) + stT132 129 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 128
    simpa using h
  have hprev := st132_p128
  have hstep := st132_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p130 : ((19700419412189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT132 (i+1))
      = (∑ i ∈ Finset.range 129, stT132 (i+1)) + stT132 130 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 129
    simpa using h
  have hprev := st132_p129
  have hstep := st132_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p131 : ((9413336674027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT132 (i+1))
      = (∑ i ∈ Finset.range 130, stT132 (i+1)) + stT132 131 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 130
    simpa using h
  have hprev := st132_p130
  have hstep := st132_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p132 : ((18360948213101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT132 (i+1))
      = (∑ i ∈ Finset.range 131, stT132 (i+1)) + stT132 132 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 131
    simpa using h
  have hprev := st132_p131
  have hstep := st132_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p133 : ((9361854666507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT132 (i+1))
      = (∑ i ∈ Finset.range 132, stT132 (i+1)) + stT132 133 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 132
    simpa using h
  have hprev := st132_p132
  have hstep := st132_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p134 : ((9788894854287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT132 (i+1))
      = (∑ i ∈ Finset.range 133, stT132 (i+1)) + stT132 134 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 133
    simpa using h
  have hprev := st132_p133
  have hstep := st132_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p135 : ((1007895214921/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT132 (i+1))
      = (∑ i ∈ Finset.range 134, stT132 (i+1)) + stT132 135 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 134
    simpa using h
  have hprev := st132_p134
  have hstep := st132_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p136 : ((9979329469963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT132 (i+1))
      = (∑ i ∈ Finset.range 135, stT132 (i+1)) + stT132 136 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 135
    simpa using h
  have hprev := st132_p135
  have hstep := st132_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p137 : ((9580929519193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT132 (i+1))
      = (∑ i ∈ Finset.range 136, stT132 (i+1)) + stT132 137 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 136
    simpa using h
  have hprev := st132_p136
  have hstep := st132_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p138 : ((9227400784579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT132 (i+1))
      = (∑ i ∈ Finset.range 137, stT132 (i+1)) + stT132 138 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 137
    simpa using h
  have hprev := st132_p137
  have hstep := st132_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p139 : ((9215921394653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT132 (i+1))
      = (∑ i ∈ Finset.range 138, stT132 (i+1)) + stT132 139 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 138
    simpa using h
  have hprev := st132_p138
  have hstep := st132_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p140 : ((2387975873309/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT132 (i+1))
      = (∑ i ∈ Finset.range 139, stT132 (i+1)) + stT132 140 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 139
    simpa using h
  have hprev := st132_p139
  have hstep := st132_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p141 : ((9955624787579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT132 (i+1))
      = (∑ i ∈ Finset.range 140, stT132 (i+1)) + stT132 141 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 140
    simpa using h
  have hprev := st132_p140
  have hstep := st132_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p142 : ((2019896445937/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT132 (i+1))
      = (∑ i ∈ Finset.range 141, stT132 (i+1)) + stT132 142 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 141
    simpa using h
  have hprev := st132_p141
  have hstep := st132_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p143 : ((19743219550557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT132 (i+1))
      = (∑ i ∈ Finset.range 142, stT132 (i+1)) + stT132 143 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 142
    simpa using h
  have hprev := st132_p142
  have hstep := st132_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p144 : ((18912163052379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT132 (i+1))
      = (∑ i ∈ Finset.range 143, stT132 (i+1)) + stT132 144 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 143
    simpa using h
  have hprev := st132_p143
  have hstep := st132_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p145 : ((18357133435859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT132 (i+1))
      = (∑ i ∈ Finset.range 144, stT132 (i+1)) + stT132 145 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 144
    simpa using h
  have hprev := st132_p144
  have hstep := st132_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p146 : ((9250718563237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT132 (i+1))
      = (∑ i ∈ Finset.range 145, stT132 (i+1)) + stT132 146 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 145
    simpa using h
  have hprev := st132_p145
  have hstep := st132_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p147 : ((240342373061/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT132 (i+1))
      = (∑ i ∈ Finset.range 146, stT132 (i+1)) + stT132 147 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 146
    simpa using h
  have hprev := st132_p146
  have hstep := st132_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p148 : ((1998431068987/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT132 (i+1))
      = (∑ i ∈ Finset.range 147, stT132 (i+1)) + stT132 148 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 147
    simpa using h
  have hprev := st132_p147
  have hstep := st132_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p149 : ((10105902292361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT132 (i+1))
      = (∑ i ∈ Finset.range 148, stT132 (i+1)) + stT132 149 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 148
    simpa using h
  have hprev := st132_p148
  have hstep := st132_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p150 : ((9874864668247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT132 (i+1))
      = (∑ i ∈ Finset.range 149, stT132 (i+1)) + stT132 150 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 149
    simpa using h
  have hprev := st132_p149
  have hstep := st132_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p151 : ((3787871487301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT132 (i+1))
      = (∑ i ∈ Finset.range 150, stT132 (i+1)) + stT132 151 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 150
    simpa using h
  have hprev := st132_p150
  have hstep := st132_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p152 : ((18362162439301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT132 (i+1))
      = (∑ i ∈ Finset.range 151, stT132 (i+1)) + stT132 152 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 151
    simpa using h
  have hprev := st132_p151
  have hstep := st132_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p153 : ((18421776881329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT132 (i+1))
      = (∑ i ∈ Finset.range 152, stT132 (i+1)) + stT132 153 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 152
    simpa using h
  have hprev := st132_p152
  have hstep := st132_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p154 : ((19069524002877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT132 (i+1))
      = (∑ i ∈ Finset.range 153, stT132 (i+1)) + stT132 154 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 153
    simpa using h
  have hprev := st132_p153
  have hstep := st132_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p155 : ((19853801492419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT132 (i+1))
      = (∑ i ∈ Finset.range 154, stT132 (i+1)) + stT132 155 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 154
    simpa using h
  have hprev := st132_p154
  have hstep := st132_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p156 : ((20240799643459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT132 (i+1))
      = (∑ i ∈ Finset.range 155, stT132 (i+1)) + stT132 156 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 155
    simpa using h
  have hprev := st132_p155
  have hstep := st132_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p157 : ((19975430927437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT132 (i+1))
      = (∑ i ∈ Finset.range 156, stT132 (i+1)) + stT132 157 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 156
    simpa using h
  have hprev := st132_p156
  have hstep := st132_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p158 : ((3848145190883/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT132 (i+1))
      = (∑ i ∈ Finset.range 157, stT132 (i+1)) + stT132 158 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 157
    simpa using h
  have hprev := st132_p157
  have hstep := st132_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p159 : ((18522840216027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT132 (i+1))
      = (∑ i ∈ Finset.range 158, stT132 (i+1)) + stT132 159 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 158
    simpa using h
  have hprev := st132_p158
  have hstep := st132_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p160 : ((18286008370557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT132 (i+1))
      = (∑ i ∈ Finset.range 159, stT132 (i+1)) + stT132 160 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 159
    simpa using h
  have hprev := st132_p159
  have hstep := st132_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p161 : ((18676357677337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT132 (i+1))
      = (∑ i ∈ Finset.range 160, stT132 (i+1)) + stT132 161 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 160
    simpa using h
  have hprev := st132_p160
  have hstep := st132_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p162 : ((19440358074373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT132 (i+1))
      = (∑ i ∈ Finset.range 161, stT132 (i+1)) + stT132 162 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 161
    simpa using h
  have hprev := st132_p161
  have hstep := st132_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p163 : ((20096729171113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT132 (i+1))
      = (∑ i ∈ Finset.range 162, stT132 (i+1)) + stT132 163 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 162
    simpa using h
  have hprev := st132_p162
  have hstep := st132_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p164 : ((20241371693357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT132 (i+1))
      = (∑ i ∈ Finset.range 163, stT132 (i+1)) + stT132 164 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 163
    simpa using h
  have hprev := st132_p163
  have hstep := st132_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p165 : ((9895745956369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT132 (i+1))
      = (∑ i ∈ Finset.range 164, stT132 (i+1)) + stT132 165 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 164
    simpa using h
  have hprev := st132_p164
  have hstep := st132_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p166 : ((1902486583781/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT132 (i+1))
      = (∑ i ∈ Finset.range 165, stT132 (i+1)) + stT132 166 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 165
    simpa using h
  have hprev := st132_p165
  have hstep := st132_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p167 : ((1840214645029/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT132 (i+1))
      = (∑ i ∈ Finset.range 166, stT132 (i+1)) + stT132 167 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 166
    simpa using h
  have hprev := st132_p166
  have hstep := st132_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p168 : ((18289039743539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT132 (i+1))
      = (∑ i ∈ Finset.range 167, stT132 (i+1)) + stT132 168 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 167
    simpa using h
  have hprev := st132_p167
  have hstep := st132_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p169 : ((18746103132629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT132 (i+1))
      = (∑ i ∈ Finset.range 168, stT132 (i+1)) + stT132 169 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 168
    simpa using h
  have hprev := st132_p168
  have hstep := st132_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p170 : ((3900749550613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT132 (i+1))
      = (∑ i ∈ Finset.range 169, stT132 (i+1)) + stT132 170 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 169
    simpa using h
  have hprev := st132_p169
  have hstep := st132_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p171 : ((5031694330647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT132 (i+1))
      = (∑ i ∈ Finset.range 170, stT132 (i+1)) + stT132 171 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 170
    simpa using h
  have hprev := st132_p170
  have hstep := st132_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p172 : ((2533154304051/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT132 (i+1))
      = (∑ i ∈ Finset.range 171, stT132 (i+1)) + stT132 172 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 171
    simpa using h
  have hprev := st132_p171
  have hstep := st132_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p173 : ((1240431866843/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT132 (i+1))
      = (∑ i ∈ Finset.range 172, stT132 (i+1)) + stT132 173 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 172
    simpa using h
  have hprev := st132_p172
  have hstep := st132_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p174 : ((19108293255689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT132 (i+1))
      = (∑ i ∈ Finset.range 173, stT132 (i+1)) + stT132 174 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 173
    simpa using h
  have hprev := st132_p173
  have hstep := st132_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p175 : ((3691132995451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT132 (i+1))
      = (∑ i ∈ Finset.range 174, stT132 (i+1)) + stT132 175 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 174
    simpa using h
  have hprev := st132_p174
  have hstep := st132_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p176 : ((45600879437/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT132 (i+1))
      = (∑ i ∈ Finset.range 175, stT132 (i+1)) + stT132 176 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 175
    simpa using h
  have hprev := st132_p175
  have hstep := st132_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p177 : ((1160801991241/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT132 (i+1))
      = (∑ i ∈ Finset.range 176, stT132 (i+1)) + stT132 177 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 176
    simpa using h
  have hprev := st132_p176
  have hstep := st132_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p178 : ((19271906681529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT132 (i+1))
      = (∑ i ∈ Finset.range 177, stT132 (i+1)) + stT132 178 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 177
    simpa using h
  have hprev := st132_p177
  have hstep := st132_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p179 : ((9984277110357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT132 (i+1))
      = (∑ i ∈ Finset.range 178, stT132 (i+1)) + stT132 179 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 178
    simpa using h
  have hprev := st132_p178
  have hstep := st132_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p180 : ((10151308184437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT132 (i+1))
      = (∑ i ∈ Finset.range 179, stT132 (i+1)) + stT132 180 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 179
    simpa using h
  have hprev := st132_p179
  have hstep := st132_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p181 : ((20106821316449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT132 (i+1))
      = (∑ i ∈ Finset.range 180, stT132 (i+1)) + stT132 181 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 180
    simpa using h
  have hprev := st132_p180
  have hstep := st132_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p182 : ((19485548558949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT132 (i+1))
      = (∑ i ∈ Finset.range 181, stT132 (i+1)) + stT132 182 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 181
    simpa using h
  have hprev := st132_p181
  have hstep := st132_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p183 : ((18754183749587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT132 (i+1))
      = (∑ i ∈ Finset.range 182, stT132 (i+1)) + stT132 183 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 182
    simpa using h
  have hprev := st132_p182
  have hstep := st132_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p184 : ((18276311695017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT132 (i+1))
      = (∑ i ∈ Finset.range 183, stT132 (i+1)) + stT132 184 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 183
    simpa using h
  have hprev := st132_p183
  have hstep := st132_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p185 : ((18283831463809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT132 (i+1))
      = (∑ i ∈ Finset.range 184, stT132 (i+1)) + stT132 185 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 184
    simpa using h
  have hprev := st132_p184
  have hstep := st132_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p186 : ((9384152745767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT132 (i+1))
      = (∑ i ∈ Finset.range 185, stT132 (i+1)) + stT132 186 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 185
    simpa using h
  have hprev := st132_p185
  have hstep := st132_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p187 : ((9746134213947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT132 (i+1))
      = (∑ i ∈ Finset.range 186, stT132 (i+1)) + stT132 187 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 186
    simpa using h
  have hprev := st132_p186
  have hstep := st132_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p188 : ((2010904971213/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT132 (i+1))
      = (∑ i ∈ Finset.range 187, stT132 (i+1)) + stT132 188 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 187
    simpa using h
  have hprev := st132_p187
  have hstep := st132_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p189 : ((2032930037277/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT132 (i+1))
      = (∑ i ∈ Finset.range 188, stT132 (i+1)) + stT132 189 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 188
    simpa using h
  have hprev := st132_p188
  have hstep := st132_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p190 : ((20054192965077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT132 (i+1))
      = (∑ i ∈ Finset.range 189, stT132 (i+1)) + stT132 190 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 189
    simpa using h
  have hprev := st132_p189
  have hstep := st132_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p191 : ((2426922283019/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT132 (i+1))
      = (∑ i ∈ Finset.range 190, stT132 (i+1)) + stT132 191 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 190
    simpa using h
  have hprev := st132_p190
  have hstep := st132_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p192 : ((2338510451203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT132 (i+1))
      = (∑ i ∈ Finset.range 191, stT132 (i+1)) + stT132 192 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 191
    simpa using h
  have hprev := st132_p191
  have hstep := st132_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p193 : ((1140797614961/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT132 (i+1))
      = (∑ i ∈ Finset.range 192, stT132 (i+1)) + stT132 193 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 192
    simpa using h
  have hprev := st132_p192
  have hstep := st132_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p194 : ((1825085637619/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT132 (i+1))
      = (∑ i ∈ Finset.range 193, stT132 (i+1)) + stT132 194 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 193
    simpa using h
  have hprev := st132_p193
  have hstep := st132_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p195 : ((934945550157/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT132 (i+1))
      = (∑ i ∈ Finset.range 194, stT132 (i+1)) + stT132 195 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 194
    simpa using h
  have hprev := st132_p194
  have hstep := st132_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p196 : ((3879203061207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT132 (i+1))
      = (∑ i ∈ Finset.range 195, stT132 (i+1)) + stT132 196 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 195
    simpa using h
  have hprev := st132_p195
  have hstep := st132_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p197 : ((4007366439627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT132 (i+1))
      = (∑ i ∈ Finset.range 196, stT132 (i+1)) + stT132 197 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 196
    simpa using h
  have hprev := st132_p196
  have hstep := st132_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p198 : ((2034605494007/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT132 (i+1))
      = (∑ i ∈ Finset.range 197, stT132 (i+1)) + stT132 198 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 197
    simpa using h
  have hprev := st132_p197
  have hstep := st132_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p199 : ((2019494256413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT132 (i+1))
      = (∑ i ∈ Finset.range 198, stT132 (i+1)) + stT132 199 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 198
    simpa using h
  have hprev := st132_p198
  have hstep := st132_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p200 : ((19651530127523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT132 (i+1))
      = (∑ i ∈ Finset.range 199, stT132 (i+1)) + stT132 200 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 199
    simpa using h
  have hprev := st132_p199
  have hstep := st132_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p201 : ((18946605924431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT132 (i+1))
      = (∑ i ∈ Finset.range 200, stT132 (i+1)) + stT132 201 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 200
    simpa using h
  have hprev := st132_p200
  have hstep := st132_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p202 : ((18373543646979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT132 (i+1))
      = (∑ i ∈ Finset.range 201, stT132 (i+1)) + stT132 202 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 201
    simpa using h
  have hprev := st132_p201
  have hstep := st132_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p203 : ((9083087357157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT132 (i+1))
      = (∑ i ∈ Finset.range 202, stT132 (i+1)) + stT132 203 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 202
    simpa using h
  have hprev := st132_p202
  have hstep := st132_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p204 : ((9202703125527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT132 (i+1))
      = (∑ i ∈ Finset.range 203, stT132 (i+1)) + stT132 204 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 203
    simpa using h
  have hprev := st132_p203
  have hstep := st132_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p205 : ((2373862427703/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT132 (i+1))
      = (∑ i ∈ Finset.range 204, stT132 (i+1)) + stT132 205 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 204
    simpa using h
  have hprev := st132_p204
  have hstep := st132_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p206 : ((3937218110299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT132 (i+1))
      = (∑ i ∈ Finset.range 205, stT132 (i+1)) + stT132 206 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 205
    simpa using h
  have hprev := st132_p205
  have hstep := st132_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p207 : ((20215406441039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT132 (i+1))
      = (∑ i ∈ Finset.range 206, stT132 (i+1)) + stT132 207 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 206
    simpa using h
  have hprev := st132_p206
  have hstep := st132_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p208 : ((20373199176539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT132 (i+1))
      = (∑ i ∈ Finset.range 207, stT132 (i+1)) + stT132 208 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 207
    simpa using h
  have hprev := st132_p207
  have hstep := st132_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p209 : ((20101593131499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT132 (i+1))
      = (∑ i ∈ Finset.range 208, stT132 (i+1)) + stT132 209 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 208
    simpa using h
  have hprev := st132_p208
  have hstep := st132_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p210 : ((19508712576609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT132 (i+1))
      = (∑ i ∈ Finset.range 209, stT132 (i+1)) + stT132 210 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 209
    simpa using h
  have hprev := st132_p209
  have hstep := st132_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p211 : ((9411512106229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT132 (i+1))
      = (∑ i ∈ Finset.range 210, stT132 (i+1)) + stT132 211 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 210
    simpa using h
  have hprev := st132_p210
  have hstep := st132_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p212 : ((9151954142863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT132 (i+1))
      = (∑ i ∈ Finset.range 211, stT132 (i+1)) + stT132 212 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 211
    simpa using h
  have hprev := st132_p211
  have hstep := st132_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p213 : ((18143874857697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT132 (i+1))
      = (∑ i ∈ Finset.range 212, stT132 (i+1)) + stT132 213 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 212
    simpa using h
  have hprev := st132_p212
  have hstep := st132_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p214 : ((9199519340701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT132 (i+1))
      = (∑ i ∈ Finset.range 213, stT132 (i+1)) + stT132 214 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 213
    simpa using h
  have hprev := st132_p213
  have hstep := st132_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p215 : ((9486067303729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT132 (i+1))
      = (∑ i ∈ Finset.range 214, stT132 (i+1)) + stT132 215 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 214
    simpa using h
  have hprev := st132_p214
  have hstep := st132_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p216 : ((4912994355341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT132 (i+1))
      = (∑ i ∈ Finset.range 215, stT132 (i+1)) + stT132 216 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 215
    simpa using h
  have hprev := st132_p215
  have hstep := st132_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p217 : ((2524075673593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT132 (i+1))
      = (∑ i ∈ Finset.range 216, stT132 (i+1)) + stT132 217 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 216
    simpa using h
  have hprev := st132_p216
  have hstep := st132_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p218 : ((1275130094489/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT132 (i+1))
      = (∑ i ∈ Finset.range 217, stT132 (i+1)) + stT132 218 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 217
    simpa using h
  have hprev := st132_p217
  have hstep := st132_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p219 : ((5052264913769/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT132 (i+1))
      = (∑ i ∈ Finset.range 218, stT132 (i+1)) + stT132 219 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 218
    simpa using h
  have hprev := st132_p218
  have hstep := st132_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p220 : ((4921175656919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT132 (i+1))
      = (∑ i ∈ Finset.range 219, stT132 (i+1)) + stT132 220 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 219
    simpa using h
  have hprev := st132_p219
  have hstep := st132_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p221 : ((19014209760869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT132 (i+1))
      = (∑ i ∈ Finset.range 220, stT132 (i+1)) + stT132 221 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 220
    simpa using h
  have hprev := st132_p220
  have hstep := st132_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p222 : ((18429997123277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT132 (i+1))
      = (∑ i ∈ Finset.range 221, stT132 (i+1)) + stT132 222 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 221
    simpa using h
  have hprev := st132_p221
  have hstep := st132_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p223 : ((18131015809177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT132 (i+1))
      = (∑ i ∈ Finset.range 222, stT132 (i+1)) + stT132 223 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 222
    simpa using h
  have hprev := st132_p222
  have hstep := st132_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p224 : ((9108084284131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT132 (i+1))
      = (∑ i ∈ Finset.range 223, stT132 (i+1)) + stT132 224 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 223
    simpa using h
  have hprev := st132_p223
  have hstep := st132_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p225 : ((2331703433017/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT132 (i+1))
      = (∑ i ∈ Finset.range 224, stT132 (i+1)) + stT132 225 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 224
    simpa using h
  have hprev := st132_p224
  have hstep := st132_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p226 : ((2411844193837/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT132 (i+1))
      = (∑ i ∈ Finset.range 225, stT132 (i+1)) + stT132 226 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 225
    simpa using h
  have hprev := st132_p225
  have hstep := st132_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p227 : ((9963079938913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT132 (i+1))
      = (∑ i ∈ Finset.range 226, stT132 (i+1)) + stT132 227 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 226
    simpa using h
  have hprev := st132_p226
  have hstep := st132_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p228 : ((5085303971903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT132 (i+1))
      = (∑ i ∈ Finset.range 227, stT132 (i+1)) + stT132 228 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 227
    simpa using h
  have hprev := st132_p227
  have hstep := st132_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p229 : ((10203484630533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT132 (i+1))
      = (∑ i ∈ Finset.range 228, stT132 (i+1)) + stT132 229 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 228
    simpa using h
  have hprev := st132_p228
  have hstep := st132_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p230 : ((20105114529981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT132 (i+1))
      = (∑ i ∈ Finset.range 229, stT132 (i+1)) + stT132 230 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 229
    simpa using h
  have hprev := st132_p229
  have hstep := st132_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p231 : ((19534976751613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT132 (i+1))
      = (∑ i ∈ Finset.range 230, stT132 (i+1)) + stT132 231 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 230
    simpa using h
  have hprev := st132_p230
  have hstep := st132_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p232 : ((18879151494187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT132 (i+1))
      = (∑ i ∈ Finset.range 231, stT132 (i+1)) + stT132 232 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 231
    simpa using h
  have hprev := st132_p231
  have hstep := st132_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p233 : ((18344127114349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT132 (i+1))
      = (∑ i ∈ Finset.range 232, stT132 (i+1)) + stT132 233 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 232
    simpa using h
  have hprev := st132_p232
  have hstep := st132_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p234 : ((18095418959899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT132 (i+1))
      = (∑ i ∈ Finset.range 233, stT132 (i+1)) + stT132 234 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 233
    simpa using h
  have hprev := st132_p233
  have hstep := st132_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p235 : ((18207466078819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT132 (i+1))
      = (∑ i ∈ Finset.range 234, stT132 (i+1)) + stT132 235 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 234
    simpa using h
  have hprev := st132_p234
  have hstep := st132_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p236 : ((18643069992291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT132 (i+1))
      = (∑ i ∈ Finset.range 235, stT132 (i+1)) + stT132 236 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 235
    simpa using h
  have hprev := st132_p235
  have hstep := st132_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p237 : ((19267403236641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT132 (i+1))
      = (∑ i ∈ Finset.range 236, stT132 (i+1)) + stT132 237 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 236
    simpa using h
  have hprev := st132_p236
  have hstep := st132_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p238 : ((9945493419249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT132 (i+1))
      = (∑ i ∈ Finset.range 237, stT132 (i+1)) + stT132 238 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 237
    simpa using h
  have hprev := st132_p237
  have hstep := st132_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p239 : ((5081901163567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT132 (i+1))
      = (∑ i ∈ Finset.range 238, stT132 (i+1)) + stT132 239 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 238
    simpa using h
  have hprev := st132_p238
  have hstep := st132_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p240 : ((2556174951277/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT132 (i+1))
      = (∑ i ∈ Finset.range 239, stT132 (i+1)) + stT132 240 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 239
    simpa using h
  have hprev := st132_p239
  have hstep := st132_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p241 : ((4044612046531/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT132 (i+1))
      = (∑ i ∈ Finset.range 240, stT132 (i+1)) + stT132 241 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 240
    simpa using h
  have hprev := st132_p240
  have hstep := st132_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p242 : ((985863408319/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT132 (i+1))
      = (∑ i ∈ Finset.range 241, stT132 (i+1)) + stT132 242 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 241
    simpa using h
  have hprev := st132_p241
  have hstep := st132_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p243 : ((19080417407129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT132 (i+1))
      = (∑ i ∈ Finset.range 242, stT132 (i+1)) + stT132 243 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 242
    simpa using h
  have hprev := st132_p242
  have hstep := st132_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p244 : ((2312019150883/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT132 (i+1))
      = (∑ i ∈ Finset.range 243, stT132 (i+1)) + stT132 244 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 243
    simpa using h
  have hprev := st132_p243
  have hstep := st132_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p245 : ((18130274099057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT132 (i+1))
      = (∑ i ∈ Finset.range 244, stT132 (i+1)) + stT132 245 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 244
    simpa using h
  have hprev := st132_p244
  have hstep := st132_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p246 : ((4521087516331/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT132 (i+1))
      = (∑ i ∈ Finset.range 245, stT132 (i+1)) + stT132 246 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 245
    simpa using h
  have hprev := st132_p245
  have hstep := st132_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p247 : ((4592190980763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT132 (i+1))
      = (∑ i ∈ Finset.range 246, stT132 (i+1)) + stT132 247 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 246
    simpa using h
  have hprev := st132_p246
  have hstep := st132_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p248 : ((4725490498263/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT132 (i+1))
      = (∑ i ∈ Finset.range 247, stT132 (i+1)) + stT132 248 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 247
    simpa using h
  have hprev := st132_p247
  have hstep := st132_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p249 : ((2441884147743/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT132 (i+1))
      = (∑ i ∈ Finset.range 248, stT132 (i+1)) + stT132 249 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 248
    simpa using h
  have hprev := st132_p248
  have hstep := st132_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_p250 : ((20094191862419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT132 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT132 (i+1))
      = (∑ i ∈ Finset.range 249, stT132 (i+1)) + stT132 250 := by
    have h := Finset.sum_range_succ (fun i => stT132 (i+1)) 249
    simpa using h
  have hprev := st132_p249
  have hstep := st132_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st132_s250 :
    |Real.sin (((132 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))
      - ((467307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1215607/10000000) (δ := 3317/500000000) (ψ := -502893/1000000) 132 116
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 132`** (evaluated boundary). -/
theorem station_132_sign : hardyG ((((132:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 132 250 (by norm_num) (by norm_num)
    ((-502893/1000000 : ℚ) : ℝ)
  have hchain := st132_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT132 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((132 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-502893/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st132_c250
  have hsinb := abs_le.mp st132_s250
  have hbdy_lo : ((-9824128231401/174242500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((132 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ))) / 2
          - ((((132:ℕ)):ℝ))
            * Real.sin (((132 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-502893/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((132:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((132:ℝ) * Real.log (250:ℝ) - ((-502893/1000000 : ℚ) : ℝ))) / 2
        - ((132:ℝ)) * Real.sin ((132:ℝ) * Real.log (250:ℝ) - ((-502893/1000000 : ℚ) : ℝ))
        ≥ ((-124266393/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((132:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-124266393/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-124266393/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-124266393/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((132:ℕ)):ℝ))+1) * (((((132:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((383998269281/937500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((20094191862419/10000000000000 : ℚ) : ℝ) + ((-9824128231401/174242500000000 : ℚ) : ℝ)
      - ((383998269281/937500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-502893/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((132:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-502893/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((132:ℕ)):ℝ)))).re
      - Real.sin ((-502893/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((132:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((132:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((132:ℕ)):ℝ))
      = (((((132:ℕ)):ℝ)) * (Real.log ((((132:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((132:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_132
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
  have hθwin : |(((-502893/1000000 : ℚ) : ℝ) + ((22:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((132:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((132:ℕ)):ℝ)))
    (φ := ((-502893/1000000 : ℚ) : ℝ) + ((22:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-502893/1000000 : ℚ) : ℝ) + ((22:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-502893/1000000 : ℚ)) : ℝ) - Real.pi) + ((22:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-502893/1000000 : ℚ)) : ℝ) - Real.pi) 22).1,
    (cos_sin_shift ((((-502893/1000000 : ℚ)) : ℝ) - Real.pi) 22).2]
  exact cos_sin_flip ((-502893/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_132_sign
end AxiomAudit
