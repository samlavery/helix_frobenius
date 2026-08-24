import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 113` of the extended Hardy ladder (rung-126)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT113 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((113 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))

theorem st113_c1 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((225187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1123267/10000000) (δ := 21/100000000) (ψ := -449307/1000000) 113 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t1 : ((450349/500000 : ℚ) : ℝ) ≤ stT113 1 := by
  have hc : ((450349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450349/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((450349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c2 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-486243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7266177/10000000) (δ := 891/100000000) (ψ := -449307/1000000) 113 13
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t2 : ((-214902130889/312500000000 : ℚ) : ℝ) ≤ stT113 2 := by
  have hc : ((-121567/125000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214902130889/312500000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-121567/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c3 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((239531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2678027/10000000) (δ := 61/6250000) (ψ := -449307/1000000) 113 20
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t3 : ((345697092503/1250000000000 : ℚ) : ℝ) ≤ stT113 3 := by
  have hc : ((119753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345697092503/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((119753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c4 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((999781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26171/5000000) (δ := 659/100000000) (ψ := -449307/1000000) 113 25
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t4 : ((999731/2000000 : ℚ) : ℝ) ≤ stT113 4 := by
  have hc : ((999731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999731/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((999731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c5 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((994657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129271/5000000) (δ := 1031/100000000) (ψ := -449307/1000000) 113 29
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t5 : ((889603355189/2000000000000 : ℚ) : ℝ) ≤ stT113 5 := by
  have hc : ((994607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((889603355189/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((994607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c6 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-140771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160123/2500000) (δ := 93/12500000) (ψ := -449307/1000000) 113 32
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t6 : ((-143699319117/1250000000000 : ℚ) : ℝ) ≤ stT113 6 := by
  have hc : ((-35199/125000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143699319117/1250000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-35199/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c7 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((910763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 106417/1000000) (δ := 293/50000000) (ψ := -449307/1000000) 113 35
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t7 : ((860542731543/2500000000000 : ℚ) : ℝ) ≤ stT113 7 := by
  have hc : ((910713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((860542731543/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((910713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c8 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-490693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3685431/5000000) (δ := 133/20000000) (ψ := -449307/1000000) 113 37
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t8 : ((-433737543353/1250000000000 : ℚ) : ℝ) ≤ stT113 8 := by
  have hc : ((-245359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433737543353/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-245359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c9 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-170519/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6479321/10000000) (δ := 21/2500000) (ψ := -449307/1000000) 113 40
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t9 : ((-284215056843/1000000000000 : ℚ) : ℝ) ≤ stT113 9 := by
  have hc : ((-170529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284215056843/1000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-170529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c10 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-62117/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3788531/5000000) (δ := 1041/100000000) (ψ := -449307/1000000) 113 41
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t10 : ((-785764418579/2500000000000 : ℚ) : ℝ) ≤ stT113 10 := by
  have hc : ((-496961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-785764418579/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-496961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c11 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((329989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086261/10000000) (δ := 401/50000000) (ψ := -449307/1000000) 113 43
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t11 : ((994803368107/10000000000000 : ℚ) : ℝ) ≤ stT113 11 := by
  have hc : ((329939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((994803368107/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((329939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c12 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((17789/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3748951/10000000) (δ := 569/100000000) (ψ := -449307/1000000) 113 45
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t12 : ((102632658303/5000000000000 : ℚ) : ℝ) ≤ stT113 12 := by
  have hc : ((35553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102632658303/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((35553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c13 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((60771/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63103/200000) (δ := 1/160000) (ψ := -449307/1000000) 113 46
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t13 : ((337041267/4000000000 : ℚ) : ℝ) ≤ stT113 13 := by
  have hc : ((60761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337041267/4000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((60761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c14 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-977721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3662637/5000000) (δ := 807/100000000) (ψ := -449307/1000000) 113 48
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t14 : ((-2613203485623/10000000000000 : ℚ) : ℝ) ≤ stT113 14 := by
  have hc : ((-977771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2613203485623/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-977771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c15 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((38273/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3542751/10000000) (δ := 563/50000000) (ψ := -449307/1000000) 113 49
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t15 : ((49394075937/1250000000000 : ℚ) : ℝ) ≤ stT113 15 := by
  have hc : ((76521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49394075937/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((76521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c16 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((918141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -509291/5000000) (δ := 443/50000000) (ψ := -449307/1000000) 113 50
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t16 : ((918091/4000000 : ℚ) : ℝ) ≤ stT113 16 := by
  have hc : ((918091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((918091/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((918091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c17 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((987233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39991/1000000) (δ := 131/20000000) (ψ := -449307/1000000) 113 51
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t17 : ((598567553037/2500000000000 : ℚ) : ℝ) ≤ stT113 17 := by
  have hc : ((987183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((598567553037/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((987183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c18 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((944187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 839199/10000000) (δ := 649/100000000) (ψ := -449307/1000000) 113 52
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t18 : ((1112675840007/5000000000000 : ℚ) : ℝ) ≤ stT113 18 := by
  have hc : ((944137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1112675840007/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((944137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c19 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((246723/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16209/400000) (δ := 43/5000000) (ψ := -449307/1000000) 113 53
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t19 : ((1131985241097/5000000000000 : ℚ) : ℝ) ≤ stT113 19 := by
  have hc : ((493421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1131985241097/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((493421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c20 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((473833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -406191/5000000) (δ := 41/5000000) (ψ := -449307/1000000) 113 54
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t20 : ((66216652071/312500000000 : ℚ) : ℝ) ≤ stT113 20 := by
  have hc : ((29613/31250 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66216652071/312500000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((29613/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c21 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((22909/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -684281/2500000) (δ := 361/50000000) (ψ := -449307/1000000) 113 55
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t21 : ((49986060357/500000000000 : ℚ) : ℝ) ≤ stT113 21 := by
  have hc : ((45813/100000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49986060357/500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((45813/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c22 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-261547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5303183/10000000) (δ := 291/50000000) (ψ := -449307/1000000) 113 56
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t22 : ((-17427299893/156250000000 : ℚ) : ℝ) ≤ stT113 22 := by
  have hc : ((-65393/125000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17427299893/156250000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-65393/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c23 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-485691/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181361/250000) (δ := 971/100000000) (ψ := -449307/1000000) 113 56
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t23 : ((-50639414441/250000000000 : ℚ) : ℝ) ≤ stT113 23 := by
  have hc : ((-121429/125000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50639414441/250000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-121429/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c24 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((142483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111549/312500) (δ := 801/100000000) (ψ := -449307/1000000) 113 57
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t24 : ((290740079353/10000000000000 : ℚ) : ℝ) ≤ stT113 24 := by
  have hc : ((142433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290740079353/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((142433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c25 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((970747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303091/5000000) (δ := 87/10000000) (ψ := -449307/1000000) 113 58
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t25 : ((970697/5000000 : ℚ) : ℝ) ≤ stT113 25 := by
  have hc : ((970697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((970697/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((970697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c26 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-499413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2617147/5000000) (δ := 729/100000000) (ψ := -449307/1000000) 113 59
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t26 : ((-489763928003/5000000000000 : ℚ) : ℝ) ≤ stT113 26 := by
  have hc : ((-499463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489763928003/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-499463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c27 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-564761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5427349/10000000) (δ := 367/50000000) (ψ := -449307/1000000) 113 59
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t27 : ((-1086979334311/10000000000000 : ℚ) : ℝ) ≤ stT113 27 := by
  have hc : ((-564811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1086979334311/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-564811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c28 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1351/2000000) (δ := 519/50000000) (ψ := -449307/1000000) 113 60
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t28 : ((472429987403/2500000000000 : ℚ) : ℝ) ≤ stT113 28 := by
  have hc : ((499973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472429987403/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((499973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c29 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-10648/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290071/500000) (δ := 399/50000000) (ψ := -449307/1000000) 113 61
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t29 : ((-316388750997/2500000000000 : ℚ) : ℝ) ≤ stT113 29 := by
  have hc : ((-340761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316388750997/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-340761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c30 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((15113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 471971/1250000) (δ := 181/20000000) (ψ := -449307/1000000) 113 61
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t30 : ((55139203941/5000000000000 : ℚ) : ℝ) ≤ stT113 30 := by
  have hc : ((30201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55139203941/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((30201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c31 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((120551/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266907/1000000) (δ := 1087/100000000) (ψ := -449307/1000000) 113 62
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t31 : ((432987069081/5000000000000 : ℚ) : ℝ) ≤ stT113 31 := by
  have hc : ((241077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432987069081/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((241077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c32 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-812937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6299937/10000000) (δ := 1117/100000000) (ψ := -449307/1000000) 113 62
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t32 : ((-1437171590029/10000000000000 : ℚ) : ℝ) ≤ stT113 32 := by
  have hc : ((-812987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1437171590029/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-812987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c33 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((59961/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -715033/10000000) (δ := 667/100000000) (ψ := -449307/1000000) 113 63
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t33 : ((104373229811/625000000000 : ℚ) : ℝ) ≤ stT113 33 := by
  have hc : ((479663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104373229811/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((479663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c34 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-99853/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7718429/10000000) (δ := 443/50000000) (ψ := -449307/1000000) 113 63
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t34 : ((-42813767997/250000000000 : ℚ) : ℝ) ≤ stT113 34 := by
  have hc : ((-49929/50000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42813767997/250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-49929/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c35 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((996819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39889/2000000) (δ := 667/100000000) (ψ := -449307/1000000) 113 64
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t35 : ((421211653713/2500000000000 : ℚ) : ℝ) ≤ stT113 35 := by
  have hc : ((996769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421211653713/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((996769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c36 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-992629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1510049/2000000) (δ := 141/20000000) (ψ := -449307/1000000) 113 65
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t36 : ((-1654465330893/10000000000000 : ℚ) : ℝ) ≤ stT113 36 := by
  have hc : ((-992679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1654465330893/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-992679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c37 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((498557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37993/2000000) (δ := 201/20000000) (ψ := -449307/1000000) 113 65
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t37 : ((204895281037/1250000000000 : ℚ) : ℝ) ≤ stT113 37 := by
  have hc : ((124633/125000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204895281037/1250000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((124633/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c38 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-998643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1544749/2000000) (δ := 167/25000000) (ψ := -449307/1000000) 113 65
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t38 : ((-324018952999/2000000000000 : ℚ) : ℝ) ≤ stT113 38 := by
  have hc : ((-998693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324018952999/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-998693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c39 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((193357/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5048/78125) (δ := 161/25000000) (ψ := -449307/1000000) 113 66
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t39 : ((309602877507/2000000000000 : ℚ) : ℝ) ≤ stT113 39 := by
  have hc : ((193347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309602877507/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((193347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c40 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-107269/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6506137/10000000) (δ := 589/100000000) (ψ := -449307/1000000) 113 66
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t40 : ((-678468326039/5000000000000 : ℚ) : ℝ) ≤ stT113 40 := by
  have hc : ((-429101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-678468326039/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-429101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c41 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((12581/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2226163/10000000) (δ := 37/5000000) (ψ := -449307/1000000) 113 67
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t41 : ((982332573/10000000000 : ℚ) : ℝ) ≤ stT113 41 := by
  have hc : ((629/1000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((982332573/10000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((629/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c42 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-258783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 916279/2000000) (δ := 953/100000000) (ψ := -449307/1000000) 113 67
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t42 : ((-199694059661/5000000000000 : ℚ) : ℝ) ≤ stT113 42 := by
  have hc : ((-258833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199694059661/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-258833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c43 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-219093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4479203/10000000) (δ := 993/100000000) (ψ := -449307/1000000) 113 68
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t43 : ((-167095003499/5000000000000 : ℚ) : ℝ) ≤ stT113 43 := by
  have hc : ((-219143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167095003499/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-219143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c44 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((692293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251917/1250000) (δ := 783/100000000) (ψ := -449307/1000000) 113 68
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t44 : ((260898772027/2500000000000 : ℚ) : ℝ) ≤ stT113 44 := by
  have hc : ((692243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260898772027/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((692243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c45 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-979269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1468809/2000000) (δ := 1001/100000000) (ψ := -449307/1000000) 113 69
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t45 : ((-182485323141/1250000000000 : ℚ) : ℝ) ≤ stT113 45 := by
  have hc : ((-979319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182485323141/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-979319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c46 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((898699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283751/2500000) (δ := 1071/100000000) (ψ := -449307/1000000) 113 69
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t46 : ((1324985159931/10000000000000 : ℚ) : ℝ) ≤ stT113 46 := by
  have hc : ((898649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1324985159931/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((898649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c47 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-394389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4940499/10000000) (δ := 283/25000000) (ψ := -449307/1000000) 113 69
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t47 : ((-11506968947/200000000000 : ℚ) : ℝ) ≤ stT113 47 := by
  have hc : ((-394439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11506968947/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-394439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c48 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-349609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1204969/2500000) (δ := 1021/100000000) (ψ := -449307/1000000) 113 70
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t48 : ((-31543088049/625000000000 : ℚ) : ℝ) ≤ stT113 48 := by
  have hc : ((-349659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31543088049/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-349659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c49 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((920269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62817/625000) (δ := 67/6250000) (ψ := -449307/1000000) 113 70
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t49 : ((1314598177049/10000000000000 : ℚ) : ℝ) ≤ stT113 49 := by
  have hc : ((920219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1314598177049/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((920219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c50 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-897531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6712337/10000000) (δ := 1101/100000000) (ψ := -449307/1000000) 113 70
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t50 : ((-634685808167/5000000000000 : ℚ) : ℝ) ≤ stT113 50 := by
  have hc : ((-897581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634685808167/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-897581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c51 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((208697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -425173/1250000) (δ := 791/100000000) (ψ := -449307/1000000) 113 71
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t51 : ((7304105529/250000000000 : ℚ) : ℝ) ≤ stT113 51 := by
  have hc : ((208647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7304105529/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((208647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c52 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((168037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83369/400000) (δ := 961/100000000) (ψ := -449307/1000000) 113 71
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t52 : ((1864063803/20000000000 : ℚ) : ℝ) ≤ stT113 52 := by
  have hc : ((336049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1864063803/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((336049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c53 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-987941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7465341/10000000) (δ := 981/100000000) (ψ := -449307/1000000) 113 71
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t53 : ((-678555182773/5000000000000 : ℚ) : ℝ) ≤ stT113 53 := by
  have hc : ((-987991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-678555182773/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-987991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c54 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((376447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -592419/2000000) (δ := 31/5000000) (ψ := -449307/1000000) 113 72
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t54 : ((512211200319/10000000000000 : ℚ) : ℝ) ≤ stT113 54 := by
  have hc : ((376397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((512211200319/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((376397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c55 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((78811/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2221537/10000000) (δ := 963/100000000) (ψ := -449307/1000000) 113 72
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t55 : ((425040984381/5000000000000 : ℚ) : ℝ) ≤ stT113 55 := by
  have hc : ((315219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425040984381/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((315219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c56 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-244143/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1827941/2500000) (δ := 993/100000000) (ψ := -449307/1000000) 113 72
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t56 : ((-652533407477/5000000000000 : ℚ) : ℝ) ≤ stT113 56 := by
  have hc : ((-488311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-652533407477/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-488311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c57 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((26347/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -849017/2500000) (δ := 191/25000000) (ψ := -449307/1000000) 113 73
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t57 : ((34889166279/1250000000000 : ℚ) : ℝ) ≤ stT113 57 := by
  have hc : ((105363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34889166279/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((105363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c58 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((410727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517099/10000000) (δ := 1029/100000000) (ψ := -449307/1000000) 113 73
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t58 : ((33704875683/312500000000 : ℚ) : ℝ) ≤ stT113 58 := by
  have hc : ((205351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33704875683/312500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((205351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c59 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-823591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1586569/2500000) (δ := 669/100000000) (ψ := -449307/1000000) 113 73
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t59 : ((-107228998149/1000000000000 : ℚ) : ℝ) ≤ stT113 59 := by
  have hc : ((-823641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107228998149/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-823641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c60 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-271233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153419/2500000) (δ := 137/20000000) (ψ := -449307/1000000) 113 74
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t60 : ((-70044999317/2000000000000 : ℚ) : ℝ) ≤ stT113 60 := by
  have hc : ((-271283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70044999317/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-271283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c61 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((3999/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13963/2500000) (δ := 143/20000000) (ψ := -449307/1000000) 113 74
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t61 : ((799989931/6250000000 : ℚ) : ℝ) ≤ stT113 61 := by
  have hc : ((9997/10000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799989931/6250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((9997/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c62 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-142489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4649449/10000000) (δ := 189/20000000) (ψ := -449307/1000000) 113 74
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t62 : ((-45248266257/1250000000000 : ℚ) : ℝ) ≤ stT113 62 := by
  have hc : ((-71257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45248266257/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-71257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c63 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-864709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3269209/5000000) (δ := 429/50000000) (ψ := -449307/1000000) 113 75
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t63 : ((-544747149219/5000000000000 : ℚ) : ℝ) ≤ stT113 63 := by
  have hc : ((-864759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544747149219/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-864759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c64 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((335291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2089507/10000000) (δ := 37/4000000) (ψ := -449307/1000000) 113 75
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t64 : ((167633/2000000 : ℚ) : ℝ) ≤ stT113 64 := by
  have hc : ((167633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167633/2000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((167633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c65 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((608863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145213/5000000) (δ := 157/20000000) (ψ := -449307/1000000) 113 75
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t65 : ((755139378111/10000000000000 : ℚ) : ℝ) ≤ stT113 65 := by
  have hc : ((608813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((755139378111/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((608813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c66 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-54843/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6603487/10000000) (δ := 329/50000000) (ψ := -449307/1000000) 113 75
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t66 : ((-108017468727/1000000000000 : ℚ) : ℝ) ≤ stT113 66 := by
  have hc : ((-438769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108017468727/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-438769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c67 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-363213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1214069/2500000) (δ := 917/100000000) (ψ := -449307/1000000) 113 76
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t67 : ((-88759318157/2000000000000 : ℚ) : ℝ) ≤ stT113 67 := by
  have hc : ((-363263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88759318157/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-363263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c68 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((192839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134203/2000000) (δ := 1107/100000000) (ψ := -449307/1000000) 113 76
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t68 : ((116919743031/1000000000000 : ℚ) : ℝ) ≤ stT113 68 := by
  have hc : ((192829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116919743031/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((192829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c69 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((37681/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726573/5000000) (δ := 1107/100000000) (ψ := -449307/1000000) 113 76
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t69 : ((22675267359/1000000000000 : ℚ) : ℝ) ≤ stT113 69 := by
  have hc : ((37671/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22675267359/1000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((37671/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c70 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-990981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1503593/2000000) (δ := 657/100000000) (ψ := -449307/1000000) 113 76
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t70 : ((-1184508991099/10000000000000 : ℚ) : ℝ) ≤ stT113 70 := by
  have hc : ((-991031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1184508991099/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-991031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c71 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-102161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4182839/10000000) (δ := 867/100000000) (ψ := -449307/1000000) 113 77
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t71 : ((-60651087501/5000000000000 : ℚ) : ℝ) ≤ stT113 71 := by
  have hc : ((-102211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60651087501/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-102211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c72 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((995707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115863/5000000) (δ := 117/12500000) (ψ := -449307/1000000) 113 77
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t72 : ((1173392726727/10000000000000 : ℚ) : ℝ) ≤ stT113 72 := by
  have hc : ((995657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1173392726727/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((995657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c73 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((2093/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3664887/10000000) (δ := 353/50000000) (ψ := -449307/1000000) 113 77
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t73 : ((612124953/50000000000 : ℚ) : ℝ) ≤ stT113 73 := by
  have hc : ((523/5000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((612124953/50000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((523/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c74 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-495233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1877121/2500000) (δ := 1027/100000000) (ψ := -449307/1000000) 113 77
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t74 : ((-287863017033/2500000000000 : ℚ) : ℝ) ≤ stT113 74 := by
  have hc : ((-247629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287863017033/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-247629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c75 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-191013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1101869/2500000) (δ := 201/20000000) (ψ := -449307/1000000) 113 78
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t75 : ((-220620637163/10000000000000 : ℚ) : ℝ) ≤ stT113 75 := by
  have hc : ((-191063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220620637163/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-191063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c76 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((964757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665699/10000000) (δ := 137/20000000) (ψ := -449307/1000000) 113 78
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t76 : ((553297088073/5000000000000 : ℚ) : ℝ) ≤ stT113 76 := by
  have hc : ((964707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((553297088073/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((964707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c77 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((352209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756791/2500000) (δ := 179/20000000) (ψ := -449307/1000000) 113 78
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t77 : ((80264431439/2000000000000 : ℚ) : ℝ) ≤ stT113 77 := by
  have hc : ((352159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80264431439/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((352159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c78 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-890369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834047/1250000) (δ := 167/20000000) (ψ := -449307/1000000) 113 78
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t78 : ((-504100922241/5000000000000 : ℚ) : ℝ) ≤ stT113 78 := by
  have hc : ((-890419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504100922241/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-890419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c79 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-567881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5436813/10000000) (δ := 71/12500000) (ψ := -449307/1000000) 113 79
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t79 : ((-19967886029/312500000000 : ℚ) : ℝ) ≤ stT113 79 := by
  have hc : ((-567931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19967886029/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-567931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c80 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((36471/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1883307/10000000) (δ := 153/20000000) (ψ := -449307/1000000) 113 79
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t80 : ((81545972921/1000000000000 : ℚ) : ℝ) ≤ stT113 80 := by
  have hc : ((72937/100000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81545972921/1000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((72937/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c81 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((198957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325211/2000000) (δ := 299/50000000) (ψ := -449307/1000000) 113 79
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t81 : ((442098844679/5000000000000 : ℚ) : ℝ) ≤ stT113 81 := by
  have hc : ((397889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442098844679/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((397889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c82 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-449447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1273089/2500000) (δ := 1/160000) (ψ := -449307/1000000) 113 79
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t82 : ((-124096682263/2500000000000 : ℚ) : ℝ) ≤ stT113 82 := by
  have hc : ((-449497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124096682263/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-449497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c83 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-241269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7191323/10000000) (δ := 537/50000000) (ψ := -449307/1000000) 113 80
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t83 : ((-529681899009/5000000000000 : ℚ) : ℝ) ≤ stT113 83 := by
  have hc : ((-482563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529681899009/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-482563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c84 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((47559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3808049/10000000) (δ := 587/50000000) (ψ := -449307/1000000) 113 80
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t84 : ((51836547301/10000000000000 : ℚ) : ℝ) ≤ stT113 84 := by
  have hc : ((47509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51836547301/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((47509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c85 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((491383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232407/5000000) (δ := 639/100000000) (ψ := -449307/1000000) 113 80
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t85 : ((66619054677/625000000000 : ℚ) : ℝ) ≤ stT113 85 := by
  have hc : ((245679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66619054677/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((245679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c86 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((421473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2839317/10000000) (δ := 1079/100000000) (ψ := -449307/1000000) 113 80
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t86 : ((454431799321/10000000000000 : ℚ) : ℝ) ≤ stT113 86 := by
  have hc : ((421423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454431799321/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((421423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c87 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-765169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6105249/10000000) (δ := 59/6250000) (ψ := -449307/1000000) 113 80
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t87 : ((-820401237747/10000000000000 : ℚ) : ℝ) ≤ stT113 87 := by
  have hc : ((-765219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820401237747/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-765219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c88 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-165971/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1593527/2500000) (δ := 1003/100000000) (ψ := -449307/1000000) 113 81
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t88 : ((-44234102481/500000000000 : ℚ) : ℝ) ≤ stT113 88 := by
  have hc : ((-165981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44234102481/500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-165981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c89 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((73403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3181983/10000000) (δ := 39/5000000) (ψ := -449307/1000000) 113 81
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t89 : ((155587419657/5000000000000 : ℚ) : ℝ) ≤ stT113 89 := by
  have hc : ((146781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155587419657/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((146781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c90 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((249987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12763/5000000) (δ := 77/10000000) (ψ := -449307/1000000) 113 81
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t90 : ((131748060327/1250000000000 : ℚ) : ℝ) ≤ stT113 90 := by
  have hc : ((499949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131748060327/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((499949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c91 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((326289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3096053/10000000) (δ := 119/10000000) (ψ := -449307/1000000) 113 81
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t91 : ((85497780969/2500000000000 : ℚ) : ℝ) ≤ stT113 91 := by
  have hc : ((326239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85497780969/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((326239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c92 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-392473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1236703/2000000) (δ := 21/2500000) (ψ := -449307/1000000) 113 81
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t92 : ((-204603908677/2500000000000 : ℚ) : ℝ) ≤ stT113 92 := by
  have hc : ((-196249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204603908677/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-196249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c93 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-425359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1617591/2500000) (δ := 13/1250000) (ψ := -449307/1000000) 113 82
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t93 : ((-6892231087/78125000000 : ℚ) : ℝ) ≤ stT113 93 := by
  have hc : ((-53173/62500 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6892231087/78125000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-53173/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c94 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((38011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689789/2000000) (δ := 91/10000000) (ψ := -449307/1000000) 113 82
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t94 : ((39195029421/2000000000000 : ℚ) : ℝ) ≤ stT113 94 := by
  have hc : ((38001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39195029421/2000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((38001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c95 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((245789/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -459499/10000000) (δ := 51/5000000) (ψ := -449307/1000000) 113 82
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t95 : ((252161281917/2500000000000 : ℚ) : ℝ) ≤ stT113 95 := by
  have hc : ((491553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252161281917/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((491553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c96 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((540759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2498643/10000000) (δ := 101/10000000) (ψ := -449307/1000000) 113 82
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t96 : ((27592920979/500000000000 : ℚ) : ℝ) ≤ stT113 96 := by
  have hc : ((540709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27592920979/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((540709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c97 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-282179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 542613/1000000) (δ := 17/2000000) (ψ := -449307/1000000) 113 82
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t97 : ((-71633746197/1250000000000 : ℚ) : ℝ) ≤ stT113 97 := by
  have hc : ((-70551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71633746197/1250000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-70551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c98 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-982409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1846093/2500000) (δ := 851/100000000) (ψ := -449307/1000000) 113 83
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t98 : ((-992433906227/10000000000000 : ℚ) : ℝ) ≤ stT113 98 := by
  have hc : ((-982459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-992433906227/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-982459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c99 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((-233557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4516327/10000000) (δ := 301/50000000) (ψ := -449307/1000000) 113 83
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t99 : ((-117391956033/5000000000000 : ℚ) : ℝ) ≤ stT113 99 := by
  have hc : ((-233607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117391956033/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-233607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_c100 :
    |Real.cos (((113 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ))
      - ((391649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1677107/10000000) (δ := 941/100000000) (ψ := -449307/1000000) 113 83
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st113_t100 : ((48952951047/625000000000 : ℚ) : ℝ) ≤ stT113 100 := by
  have hc : ((48953/62500 : ℚ) : ℝ)
      ≤ Real.cos (((113 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-449307/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st113_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48952951047/625000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((48953/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st113_p1 : ((450349/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT113 (i+1) := by
  rw [Finset.sum_range_one]
  exact st113_t1

theorem st113_p2 : ((66565994111/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT113 (i+1))
      = (∑ i ∈ Finset.range 1, stT113 (i+1)) + stT113 2 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 1
    simpa using h
  have hprev := st113_p1
  have hstep := st113_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p3 : ((611961068947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT113 (i+1))
      = (∑ i ∈ Finset.range 2, stT113 (i+1)) + stT113 3 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 2
    simpa using h
  have hprev := st113_p2
  have hstep := st113_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p4 : ((1236792943947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT113 (i+1))
      = (∑ i ∈ Finset.range 3, stT113 (i+1)) + stT113 4 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 3
    simpa using h
  have hprev := st113_p3
  have hstep := st113_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p5 : ((14342360327521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT113 (i+1))
      = (∑ i ∈ Finset.range 4, stT113 (i+1)) + stT113 5 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 4
    simpa using h
  have hprev := st113_p4
  have hstep := st113_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p6 : ((2638553154917/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT113 (i+1))
      = (∑ i ∈ Finset.range 5, stT113 (i+1)) + stT113 6 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 5
    simpa using h
  have hprev := st113_p5
  have hstep := st113_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p7 : ((16634936700757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT113 (i+1))
      = (∑ i ∈ Finset.range 6, stT113 (i+1)) + stT113 7 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 6
    simpa using h
  have hprev := st113_p6
  have hstep := st113_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p8 : ((13165036353933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT113 (i+1))
      = (∑ i ∈ Finset.range 7, stT113 (i+1)) + stT113 8 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 7
    simpa using h
  have hprev := st113_p7
  have hstep := st113_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p9 : ((10322885785503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT113 (i+1))
      = (∑ i ∈ Finset.range 8, stT113 (i+1)) + stT113 9 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 8
    simpa using h
  have hprev := st113_p8
  have hstep := st113_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p10 : ((7179828111187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT113 (i+1))
      = (∑ i ∈ Finset.range 9, stT113 (i+1)) + stT113 10 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 9
    simpa using h
  have hprev := st113_p9
  have hstep := st113_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p11 : ((4087315739647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT113 (i+1))
      = (∑ i ∈ Finset.range 10, stT113 (i+1)) + stT113 11 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 10
    simpa using h
  have hprev := st113_p10
  have hstep := st113_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p12 : ((83798967959/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT113 (i+1))
      = (∑ i ∈ Finset.range 11, stT113 (i+1)) + stT113 12 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 11
    simpa using h
  have hprev := st113_p11
  have hstep := st113_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p13 : ((46112499817/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT113 (i+1))
      = (∑ i ∈ Finset.range 12, stT113 (i+1)) + stT113 13 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 12
    simpa using h
  have hprev := st113_p12
  have hstep := st113_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p14 : ((6609296477777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT113 (i+1))
      = (∑ i ∈ Finset.range 13, stT113 (i+1)) + stT113 14 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 13
    simpa using h
  have hprev := st113_p13
  have hstep := st113_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p15 : ((7004449085273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT113 (i+1))
      = (∑ i ∈ Finset.range 14, stT113 (i+1)) + stT113 15 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 14
    simpa using h
  have hprev := st113_p14
  have hstep := st113_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p16 : ((9299676585273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT113 (i+1))
      = (∑ i ∈ Finset.range 15, stT113 (i+1)) + stT113 16 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 15
    simpa using h
  have hprev := st113_p15
  have hstep := st113_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p17 : ((11693946797421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT113 (i+1))
      = (∑ i ∈ Finset.range 16, stT113 (i+1)) + stT113 17 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 16
    simpa using h
  have hprev := st113_p16
  have hstep := st113_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p18 : ((2783859695487/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT113 (i+1))
      = (∑ i ∈ Finset.range 17, stT113 (i+1)) + stT113 18 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 17
    simpa using h
  have hprev := st113_p17
  have hstep := st113_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p19 : ((16183268959629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT113 (i+1))
      = (∑ i ∈ Finset.range 18, stT113 (i+1)) + stT113 19 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 18
    simpa using h
  have hprev := st113_p18
  have hstep := st113_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p20 : ((18302201825901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT113 (i+1))
      = (∑ i ∈ Finset.range 19, stT113 (i+1)) + stT113 20 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 19
    simpa using h
  have hprev := st113_p19
  have hstep := st113_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p21 : ((19301923033041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT113 (i+1))
      = (∑ i ∈ Finset.range 20, stT113 (i+1)) + stT113 21 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 20
    simpa using h
  have hprev := st113_p20
  have hstep := st113_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p22 : ((18186575839889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT113 (i+1))
      = (∑ i ∈ Finset.range 21, stT113 (i+1)) + stT113 22 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 21
    simpa using h
  have hprev := st113_p21
  have hstep := st113_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p23 : ((16160999262249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT113 (i+1))
      = (∑ i ∈ Finset.range 22, stT113 (i+1)) + stT113 23 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 22
    simpa using h
  have hprev := st113_p22
  have hstep := st113_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p24 : ((8225869670801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT113 (i+1))
      = (∑ i ∈ Finset.range 23, stT113 (i+1)) + stT113 24 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 23
    simpa using h
  have hprev := st113_p23
  have hstep := st113_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p25 : ((9196566670801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT113 (i+1))
      = (∑ i ∈ Finset.range 24, stT113 (i+1)) + stT113 25 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 24
    simpa using h
  have hprev := st113_p24
  have hstep := st113_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p26 : ((4353401371399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT113 (i+1))
      = (∑ i ∈ Finset.range 25, stT113 (i+1)) + stT113 26 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 25
    simpa using h
  have hprev := st113_p25
  have hstep := st113_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p27 : ((3265325230257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT113 (i+1))
      = (∑ i ∈ Finset.range 26, stT113 (i+1)) + stT113 27 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 26
    simpa using h
  have hprev := st113_p26
  have hstep := st113_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p28 : ((18216346100897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT113 (i+1))
      = (∑ i ∈ Finset.range 27, stT113 (i+1)) + stT113 28 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 27
    simpa using h
  have hprev := st113_p27
  have hstep := st113_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p29 : ((16950791096909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT113 (i+1))
      = (∑ i ∈ Finset.range 28, stT113 (i+1)) + stT113 29 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 28
    simpa using h
  have hprev := st113_p28
  have hstep := st113_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p30 : ((17061069504791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT113 (i+1))
      = (∑ i ∈ Finset.range 29, stT113 (i+1)) + stT113 30 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 29
    simpa using h
  have hprev := st113_p29
  have hstep := st113_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p31 : ((17927043642953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT113 (i+1))
      = (∑ i ∈ Finset.range 30, stT113 (i+1)) + stT113 31 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 30
    simpa using h
  have hprev := st113_p30
  have hstep := st113_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p32 : ((4122468013231/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT113 (i+1))
      = (∑ i ∈ Finset.range 31, stT113 (i+1)) + stT113 32 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 31
    simpa using h
  have hprev := st113_p31
  have hstep := st113_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p33 : ((181598437299/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT113 (i+1))
      = (∑ i ∈ Finset.range 32, stT113 (i+1)) + stT113 33 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 32
    simpa using h
  have hprev := st113_p32
  have hstep := st113_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p34 : ((822364650501/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT113 (i+1))
      = (∑ i ∈ Finset.range 33, stT113 (i+1)) + stT113 34 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 33
    simpa using h
  have hprev := st113_p33
  have hstep := st113_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p35 : ((2266517453109/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT113 (i+1))
      = (∑ i ∈ Finset.range 34, stT113 (i+1)) + stT113 35 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 34
    simpa using h
  have hprev := st113_p34
  have hstep := st113_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p36 : ((16477674293979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT113 (i+1))
      = (∑ i ∈ Finset.range 35, stT113 (i+1)) + stT113 36 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 35
    simpa using h
  have hprev := st113_p35
  have hstep := st113_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p37 : ((724673461691/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT113 (i+1))
      = (∑ i ∈ Finset.range 36, stT113 (i+1)) + stT113 37 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 36
    simpa using h
  have hprev := st113_p36
  have hstep := st113_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p38 : ((25776159027/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT113 (i+1))
      = (∑ i ∈ Finset.range 37, stT113 (i+1)) + stT113 38 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 37
    simpa using h
  have hprev := st113_p37
  have hstep := st113_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p39 : ((3608951232963/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT113 (i+1))
      = (∑ i ∈ Finset.range 38, stT113 (i+1)) + stT113 39 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 38
    simpa using h
  have hprev := st113_p38
  have hstep := st113_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p40 : ((16687819512737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT113 (i+1))
      = (∑ i ∈ Finset.range 39, stT113 (i+1)) + stT113 40 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 39
    simpa using h
  have hprev := st113_p39
  have hstep := st113_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p41 : ((17670152085737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT113 (i+1))
      = (∑ i ∈ Finset.range 40, stT113 (i+1)) + stT113 41 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 40
    simpa using h
  have hprev := st113_p40
  have hstep := st113_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p42 : ((3454152793283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT113 (i+1))
      = (∑ i ∈ Finset.range 41, stT113 (i+1)) + stT113 42 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 41
    simpa using h
  have hprev := st113_p41
  have hstep := st113_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p43 : ((16936573959417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT113 (i+1))
      = (∑ i ∈ Finset.range 42, stT113 (i+1)) + stT113 43 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 42
    simpa using h
  have hprev := st113_p42
  have hstep := st113_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p44 : ((719206761901/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT113 (i+1))
      = (∑ i ∈ Finset.range 43, stT113 (i+1)) + stT113 44 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 43
    simpa using h
  have hprev := st113_p43
  have hstep := st113_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p45 : ((16520286462397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT113 (i+1))
      = (∑ i ∈ Finset.range 44, stT113 (i+1)) + stT113 45 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 44
    simpa using h
  have hprev := st113_p44
  have hstep := st113_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p46 : ((2230658952791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT113 (i+1))
      = (∑ i ∈ Finset.range 45, stT113 (i+1)) + stT113 46 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 45
    simpa using h
  have hprev := st113_p45
  have hstep := st113_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p47 : ((8634961587489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT113 (i+1))
      = (∑ i ∈ Finset.range 46, stT113 (i+1)) + stT113 47 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 46
    simpa using h
  have hprev := st113_p46
  have hstep := st113_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p48 : ((8382616883097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT113 (i+1))
      = (∑ i ∈ Finset.range 47, stT113 (i+1)) + stT113 48 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 47
    simpa using h
  have hprev := st113_p47
  have hstep := st113_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p49 : ((18079831943243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT113 (i+1))
      = (∑ i ∈ Finset.range 48, stT113 (i+1)) + stT113 49 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 48
    simpa using h
  have hprev := st113_p48
  have hstep := st113_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p50 : ((16810460326909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT113 (i+1))
      = (∑ i ∈ Finset.range 49, stT113 (i+1)) + stT113 50 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 49
    simpa using h
  have hprev := st113_p49
  have hstep := st113_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p51 : ((17102624548069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT113 (i+1))
      = (∑ i ∈ Finset.range 50, stT113 (i+1)) + stT113 51 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 50
    simpa using h
  have hprev := st113_p50
  have hstep := st113_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p52 : ((18034656449569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT113 (i+1))
      = (∑ i ∈ Finset.range 51, stT113 (i+1)) + stT113 52 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 51
    simpa using h
  have hprev := st113_p51
  have hstep := st113_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p53 : ((16677546084023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT113 (i+1))
      = (∑ i ∈ Finset.range 52, stT113 (i+1)) + stT113 53 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 52
    simpa using h
  have hprev := st113_p52
  have hstep := st113_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p54 : ((8594878642171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT113 (i+1))
      = (∑ i ∈ Finset.range 53, stT113 (i+1)) + stT113 54 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 53
    simpa using h
  have hprev := st113_p53
  have hstep := st113_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p55 : ((1127489953319/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT113 (i+1))
      = (∑ i ∈ Finset.range 54, stT113 (i+1)) + stT113 55 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 54
    simpa using h
  have hprev := st113_p54
  have hstep := st113_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p56 : ((334695448763/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT113 (i+1))
      = (∑ i ∈ Finset.range 55, stT113 (i+1)) + stT113 56 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 55
    simpa using h
  have hprev := st113_p55
  have hstep := st113_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p57 : ((8506942884191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT113 (i+1))
      = (∑ i ∈ Finset.range 56, stT113 (i+1)) + stT113 57 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 56
    simpa using h
  have hprev := st113_p56
  have hstep := st113_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p58 : ((9046220895119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT113 (i+1))
      = (∑ i ∈ Finset.range 57, stT113 (i+1)) + stT113 58 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 57
    simpa using h
  have hprev := st113_p57
  have hstep := st113_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p59 : ((4255037952187/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT113 (i+1))
      = (∑ i ∈ Finset.range 58, stT113 (i+1)) + stT113 59 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 58
    simpa using h
  have hprev := st113_p58
  have hstep := st113_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p60 : ((16669926812163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT113 (i+1))
      = (∑ i ∈ Finset.range 59, stT113 (i+1)) + stT113 60 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 59
    simpa using h
  have hprev := st113_p59
  have hstep := st113_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p61 : ((17949910701763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT113 (i+1))
      = (∑ i ∈ Finset.range 60, stT113 (i+1)) + stT113 61 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 60
    simpa using h
  have hprev := st113_p60
  have hstep := st113_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p62 : ((17587924571707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT113 (i+1))
      = (∑ i ∈ Finset.range 61, stT113 (i+1)) + stT113 62 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 61
    simpa using h
  have hprev := st113_p61
  have hstep := st113_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p63 : ((16498430273269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT113 (i+1))
      = (∑ i ∈ Finset.range 62, stT113 (i+1)) + stT113 63 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 62
    simpa using h
  have hprev := st113_p62
  have hstep := st113_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p64 : ((17336595273269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT113 (i+1))
      = (∑ i ∈ Finset.range 63, stT113 (i+1)) + stT113 64 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 63
    simpa using h
  have hprev := st113_p63
  have hstep := st113_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p65 : ((904586732569/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT113 (i+1))
      = (∑ i ∈ Finset.range 64, stT113 (i+1)) + stT113 65 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 64
    simpa using h
  have hprev := st113_p64
  have hstep := st113_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p66 : ((1701155996411/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT113 (i+1))
      = (∑ i ∈ Finset.range 65, stT113 (i+1)) + stT113 66 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 65
    simpa using h
  have hprev := st113_p65
  have hstep := st113_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p67 : ((662710534933/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT113 (i+1))
      = (∑ i ∈ Finset.range 66, stT113 (i+1)) + stT113 67 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 66
    simpa using h
  have hprev := st113_p66
  have hstep := st113_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p68 : ((3547392160727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT113 (i+1))
      = (∑ i ∈ Finset.range 67, stT113 (i+1)) + stT113 68 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 67
    simpa using h
  have hprev := st113_p67
  have hstep := st113_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p69 : ((718548539089/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT113 (i+1))
      = (∑ i ∈ Finset.range 68, stT113 (i+1)) + stT113 69 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 68
    simpa using h
  have hprev := st113_p68
  have hstep := st113_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p70 : ((8389602243063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT113 (i+1))
      = (∑ i ∈ Finset.range 69, stT113 (i+1)) + stT113 70 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 69
    simpa using h
  have hprev := st113_p69
  have hstep := st113_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p71 : ((4164475577781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT113 (i+1))
      = (∑ i ∈ Finset.range 70, stT113 (i+1)) + stT113 71 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 70
    simpa using h
  have hprev := st113_p70
  have hstep := st113_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p72 : ((17831295037851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT113 (i+1))
      = (∑ i ∈ Finset.range 71, stT113 (i+1)) + stT113 72 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 71
    simpa using h
  have hprev := st113_p71
  have hstep := st113_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p73 : ((17953720028451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT113 (i+1))
      = (∑ i ∈ Finset.range 72, stT113 (i+1)) + stT113 73 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 72
    simpa using h
  have hprev := st113_p72
  have hstep := st113_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p74 : ((16802267960319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT113 (i+1))
      = (∑ i ∈ Finset.range 73, stT113 (i+1)) + stT113 74 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 73
    simpa using h
  have hprev := st113_p73
  have hstep := st113_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p75 : ((4145411830789/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT113 (i+1))
      = (∑ i ∈ Finset.range 74, stT113 (i+1)) + stT113 75 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 74
    simpa using h
  have hprev := st113_p74
  have hstep := st113_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p76 : ((8844120749651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT113 (i+1))
      = (∑ i ∈ Finset.range 75, stT113 (i+1)) + stT113 76 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 75
    simpa using h
  have hprev := st113_p75
  have hstep := st113_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p77 : ((18089563656497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT113 (i+1))
      = (∑ i ∈ Finset.range 76, stT113 (i+1)) + stT113 77 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 76
    simpa using h
  have hprev := st113_p76
  have hstep := st113_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p78 : ((3416272362403/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT113 (i+1))
      = (∑ i ∈ Finset.range 77, stT113 (i+1)) + stT113 78 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 77
    simpa using h
  have hprev := st113_p77
  have hstep := st113_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p79 : ((16442389459087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT113 (i+1))
      = (∑ i ∈ Finset.range 78, stT113 (i+1)) + stT113 79 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 78
    simpa using h
  have hprev := st113_p78
  have hstep := st113_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p80 : ((17257849188297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT113 (i+1))
      = (∑ i ∈ Finset.range 79, stT113 (i+1)) + stT113 80 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 79
    simpa using h
  have hprev := st113_p79
  have hstep := st113_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p81 : ((3628409375531/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT113 (i+1))
      = (∑ i ∈ Finset.range 80, stT113 (i+1)) + stT113 81 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 80
    simpa using h
  have hprev := st113_p80
  have hstep := st113_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p82 : ((17645660148603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT113 (i+1))
      = (∑ i ∈ Finset.range 81, stT113 (i+1)) + stT113 82 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 81
    simpa using h
  have hprev := st113_p81
  have hstep := st113_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p83 : ((3317259270117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT113 (i+1))
      = (∑ i ∈ Finset.range 82, stT113 (i+1)) + stT113 83 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 82
    simpa using h
  have hprev := st113_p82
  have hstep := st113_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p84 : ((8319066448943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT113 (i+1))
      = (∑ i ∈ Finset.range 83, stT113 (i+1)) + stT113 84 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 83
    simpa using h
  have hprev := st113_p83
  have hstep := st113_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p85 : ((8852018886359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT113 (i+1))
      = (∑ i ∈ Finset.range 84, stT113 (i+1)) + stT113 85 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 84
    simpa using h
  have hprev := st113_p84
  have hstep := st113_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p86 : ((18158469572039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT113 (i+1))
      = (∑ i ∈ Finset.range 85, stT113 (i+1)) + stT113 86 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 85
    simpa using h
  have hprev := st113_p85
  have hstep := st113_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p87 : ((4334517083573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT113 (i+1))
      = (∑ i ∈ Finset.range 86, stT113 (i+1)) + stT113 87 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 86
    simpa using h
  have hprev := st113_p86
  have hstep := st113_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p88 : ((128542080349/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT113 (i+1))
      = (∑ i ∈ Finset.range 87, stT113 (i+1)) + stT113 88 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 87
    simpa using h
  have hprev := st113_p87
  have hstep := st113_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p89 : ((8382280561993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT113 (i+1))
      = (∑ i ∈ Finset.range 88, stT113 (i+1)) + stT113 89 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 88
    simpa using h
  have hprev := st113_p88
  have hstep := st113_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p90 : ((8909272803301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT113 (i+1))
      = (∑ i ∈ Finset.range 89, stT113 (i+1)) + stT113 90 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 89
    simpa using h
  have hprev := st113_p89
  have hstep := st113_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p91 : ((9080268365239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT113 (i+1))
      = (∑ i ∈ Finset.range 90, stT113 (i+1)) + stT113 91 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 90
    simpa using h
  have hprev := st113_p90
  have hstep := st113_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p92 : ((1734212109577/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT113 (i+1))
      = (∑ i ∈ Finset.range 91, stT113 (i+1)) + stT113 92 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 91
    simpa using h
  have hprev := st113_p91
  have hstep := st113_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p93 : ((8229957758317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT113 (i+1))
      = (∑ i ∈ Finset.range 92, stT113 (i+1)) + stT113 93 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 92
    simpa using h
  have hprev := st113_p92
  have hstep := st113_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p94 : ((16655890663739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT113 (i+1))
      = (∑ i ∈ Finset.range 93, stT113 (i+1)) + stT113 94 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 93
    simpa using h
  have hprev := st113_p93
  have hstep := st113_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p95 : ((17664535791407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT113 (i+1))
      = (∑ i ∈ Finset.range 94, stT113 (i+1)) + stT113 95 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 94
    simpa using h
  have hprev := st113_p94
  have hstep := st113_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p96 : ((18216394210987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT113 (i+1))
      = (∑ i ∈ Finset.range 95, stT113 (i+1)) + stT113 96 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 95
    simpa using h
  have hprev := st113_p95
  have hstep := st113_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p97 : ((17643324241411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT113 (i+1))
      = (∑ i ∈ Finset.range 96, stT113 (i+1)) + stT113 97 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 96
    simpa using h
  have hprev := st113_p96
  have hstep := st113_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p98 : ((1040680645949/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT113 (i+1))
      = (∑ i ∈ Finset.range 97, stT113 (i+1)) + stT113 98 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 97
    simpa using h
  have hprev := st113_p97
  have hstep := st113_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p99 : ((8208053211559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT113 (i+1))
      = (∑ i ∈ Finset.range 98, stT113 (i+1)) + stT113 99 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 98
    simpa using h
  have hprev := st113_p98
  have hstep := st113_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st113_p100 : ((1719935363987/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT113 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT113 (i+1))
      = (∑ i ∈ Finset.range 99, stT113 (i+1)) + stT113 100 := by
    have h := Finset.sum_range_succ (fun i => stT113 (i+1)) 99
    simpa using h
  have hprev := st113_p99
  have hstep := st113_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 113`.** -/
theorem station_113_sign : 0 < hardyG (((113:ℕ)):ℝ) := by
  have hcore := phase_station_lower 113 100 (by norm_num) (by norm_num)
    ((-449307/1000000 : ℚ) : ℝ)
  have hchain := st113_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT113 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((113:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-449307/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((113:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((113:ℕ)):ℝ)+1) * ((((113:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((11276343/9040000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1719935363987/1000000000000 : ℚ) : ℝ) - ((11276343/9040000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-449307/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((113:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-449307/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((113:ℕ)):ℝ))).re
      - Real.sin ((-449307/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((113:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((113:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((113:ℕ)):ℝ)
      = ((((113:ℕ)):ℝ) * (Real.log (((113:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((113:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_113
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
  have hθwin : |(((-449307/1000000 : ℚ) : ℝ) + ((17:ℤ)) * (2*Real.pi)) - theta (((113:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((113:ℕ)):ℝ))
    (φ := ((-449307/1000000 : ℚ) : ℝ) + ((17:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-449307/1000000 : ℚ)) : ℝ) 17).1,
    (cos_sin_shift (((-449307/1000000 : ℚ)) : ℝ) 17).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_113_sign
end AxiomAudit
