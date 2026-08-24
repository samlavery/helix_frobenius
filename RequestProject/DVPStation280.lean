import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 280` (rung-280.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT280 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((280 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-188847/125000 : ℚ) : ℝ))

theorem st280_c1 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((3749/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188847/500000) (δ := 1/1000000000) (ψ := -188847/125000) 280 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t1 : ((29967/500000 : ℚ) : ℝ) ≤ stT280 1 := by
  have hc : ((29967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29967/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((29967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c2 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((687153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508271/2500000) (δ := 3531/250000000) (ψ := -188847/125000) 280 31
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t2 : ((4858551348901/10000000000000 : ℚ) : ℝ) ≤ stT280 2 := by
  have hc : ((687103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4858551348901/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((687103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c3 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((79749/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623063/2000000) (δ := 14053/1000000000) (ψ := -188847/125000) 280 49
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t3 : ((460358842223/2500000000000 : ℚ) : ℝ) ≤ stT280 3 := by
  have hc : ((159473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((460358842223/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((159473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c4 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((496657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144631/5000000) (δ := 3539/250000000) (ψ := -188847/125000) 280 62
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t4 : ((62079/125000 : ℚ) : ℝ) ≤ stT280 4 := by
  have hc : ((62079/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62079/125000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((62079/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c5 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((194459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11797/200000) (δ := 7059/500000000) (ψ := -188847/125000) 280 72
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t5 : ((173920435723/400000000000 : ℚ) : ℝ) ≤ stT280 5 := by
  have hc : ((194449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173920435723/400000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((194449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c6 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((853257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 685747/5000000) (δ := 443/31250000) (ψ := -188847/125000) 280 80
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t6 : ((1741601109887/5000000000000 : ℚ) : ℝ) ≤ stT280 6 := by
  have hc : ((853207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1741601109887/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((853207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c7 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((963369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678759/10000000) (δ := 7063/500000000) (ψ := -188847/125000) 280 87
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t7 : ((910250719609/2500000000000 : ℚ) : ℝ) ≤ stT280 7 := by
  have hc : ((963319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((910250719609/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((963319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c8 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((417731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1454559/10000000) (δ := 7017/500000000) (ψ := -188847/125000) 280 93
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t8 : ((738406673649/2500000000000 : ℚ) : ℝ) ≤ stT280 8 := by
  have hc : ((208853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((738406673649/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((208853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c9 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((69473/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98149/400000) (δ := 2821/200000000) (ψ := -188847/125000) 280 98
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t9 : ((926223240711/5000000000000 : ℚ) : ℝ) ≤ stT280 9 := by
  have hc : ((277867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((926223240711/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((277867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c10 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((595027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1166871/5000000) (δ := 7081/500000000) (ψ := -188847/125000) 280 103
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t10 : ((1881482082629/10000000000000 : ℚ) : ℝ) ≤ stT280 10 := by
  have hc : ((594977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1881482082629/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((594977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c11 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((813519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310309/2000000) (δ := 14133/1000000000) (ψ := -188847/125000) 280 107
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t11 : ((2452700956997/10000000000000 : ℚ) : ℝ) ≤ stT280 11 := by
  have hc : ((813469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2452700956997/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((813469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c12 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((98893/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46541/1250000) (δ := 2821/200000000) (ψ := -188847/125000) 280 111
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t12 : ((35683129111/125000000000 : ℚ) : ℝ) ≤ stT280 12 := by
  have hc : ((12361/12500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35683129111/125000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((12361/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c13 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-963269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7174291/10000000) (δ := 3519/250000000) (ψ := -188847/125000) 280 115
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t13 : ((-2671766209819/10000000000000 : ℚ) : ℝ) ≤ stT280 13 := by
  have hc : ((-963319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2671766209819/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-963319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c14 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((566097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2422581/10000000) (δ := 7077/500000000) (ψ := -188847/125000) 280 118
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t14 : ((378206001191/2500000000000 : ℚ) : ℝ) ≤ stT280 14 := by
  have hc : ((566047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378206001191/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((566047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c15 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((438653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15643/125000) (δ := 1417/100000000) (ψ := -188847/125000) 280 121
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t15 : ((70783264529/312500000000 : ℚ) : ℝ) ≤ stT280 15 := by
  have hc : ((109657/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70783264529/312500000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((109657/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c16 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((35917/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -159919/500000) (δ := 3523/250000000) (ψ := -188847/125000) 280 124
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t16 : ((143643/2000000 : ℚ) : ℝ) ≤ stT280 16 := by
  have hc : ((143643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143643/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((143643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c17 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-999923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7822913/10000000) (δ := 14097/1000000000) (ψ := -188847/125000) 280 126
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t17 : ((-2425291515361/10000000000000 : ℚ) : ℝ) ≤ stT280 17 := by
  have hc : ((-999973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2425291515361/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-999973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c18 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((959953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709903/10000000) (δ := 567/40000000) (ψ := -188847/125000) 280 129
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t18 : ((1131256244433/5000000000000 : ℚ) : ℝ) ≤ stT280 18 := by
  have hc : ((959903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1131256244433/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((959903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c19 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-959609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7141017/10000000) (δ := 7021/500000000) (ψ := -188847/125000) 280 131
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t19 : ((-1100804686061/5000000000000 : ℚ) : ℝ) ≤ stT280 19 := by
  have hc : ((-959659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1100804686061/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-959659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c20 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-1881/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4077563/10000000) (δ := 14039/1000000000) (ψ := -188847/125000) 280 134
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t20 : ((-16838151057/1250000000000 : ℚ) : ℝ) ≤ stT280 20 := by
  have hc : ((-30121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16838151057/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-30121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c21 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((859687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1340349/10000000) (δ := 7089/500000000) (ψ := -188847/125000) 280 136
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t21 : ((937940474693/5000000000000 : ℚ) : ℝ) ≤ stT280 21 := by
  have hc : ((859637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((937940474693/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((859637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c22 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((249261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48069/2500000) (δ := 14011/1000000000) (ψ := -188847/125000) 280 138
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t22 : ((1062799093479/5000000000000 : ℚ) : ℝ) ≤ stT280 22 := by
  have hc : ((498497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1062799093479/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((498497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c23 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((490351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -491943/10000000) (δ := 3549/250000000) (ψ := -188847/125000) 280 140
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t23 : ((63900019809/312500000000 : ℚ) : ℝ) ≤ stT280 23 := by
  have hc : ((245163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63900019809/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((245163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c24 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((662639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2116149/10000000) (δ := 14021/1000000000) (ψ := -188847/125000) 280 142
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t24 : ((1352503832949/10000000000000 : ℚ) : ℝ) ≤ stT280 24 := by
  have hc : ((662589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1352503832949/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((662589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c25 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-400327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1239169/2500000) (δ := 1771/125000000) (ψ := -188847/125000) 280 144
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t25 : ((-800754400377/10000000000000 : ℚ) : ℝ) ≤ stT280 25 := by
  have hc : ((-400377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-800754400377/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-400377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c26 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-91077/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6789851/10000000) (δ := 703/50000000) (ψ := -188847/125000) 280 145
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t26 : ((-44656639321/250000000000 : ℚ) : ℝ) ≤ stT280 26 := by
  have hc : ((-45541/50000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44656639321/250000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-45541/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c27 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((188469/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 358427/2000000) (δ := 14157/1000000000) (ψ := -188847/125000) 280 147
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t27 : ((1450738137/10000000000 : ℚ) : ℝ) ≤ stT280 27 := by
  have hc : ((376913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1450738137/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((376913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c28 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-47809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2083201/5000000) (δ := 877/62500000) (ψ := -188847/125000) 280 149
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t28 : ((-45198896691/2500000000000 : ℚ) : ℝ) ≤ stT280 28 := by
  have hc : ((-23917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45198896691/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-23917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c29 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-150157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 937909/2000000) (δ := 7039/500000000) (ψ := -188847/125000) 280 150
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t29 : ((-69720266407/1250000000000 : ℚ) : ℝ) ≤ stT280 29 := by
  have hc : ((-75091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69720266407/1250000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-75091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c30 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((364097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -748833/2500000) (δ := 1411/100000000) (ψ := -188847/125000) 280 152
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t30 : ((664655533827/10000000000000 : ℚ) : ℝ) ≤ stT280 30 := by
  have hc : ((364047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((664655533827/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((364047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c31 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-1287/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849927/2000000) (δ := 14003/1000000000) (ψ := -188847/125000) 280 153
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t31 : ((-92496781/4000000000 : ℚ) : ℝ) ≤ stT280 31 := by
  have hc : ((-103/800 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92496781/4000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-103/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c32 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-79003/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2471101/5000000) (δ := 14189/1000000000) (ψ := -188847/125000) 280 155
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t32 : ((-139676573971/2000000000000 : ℚ) : ℝ) ≤ stT280 32 := by
  have hc : ((-79013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139676573971/2000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-79013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c33 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((187461/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177991/2000000) (δ := 14081/1000000000) (ψ := -188847/125000) 280 156
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t33 : ((40788775247/250000000000 : ℚ) : ℝ) ≤ stT280 33 := by
  have hc : ((187451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40788775247/250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((187451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c34 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-758391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1519773/2500000) (δ := 14029/1000000000) (ψ := -188847/125000) 280 157
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t34 : ((-650357848413/5000000000000 : ℚ) : ℝ) ≤ stT280 34 := by
  have hc : ((-758441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-650357848413/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-758441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c35 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-432657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1009117/2000000) (δ := 177/12500000) (ψ := -188847/125000) 280 159
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t35 : ((-731408536463/10000000000000 : ℚ) : ℝ) ≤ stT280 35 := by
  have hc : ((-432707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731408536463/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-432707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c36 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((915693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -516959/5000000) (δ := 14053/1000000000) (ψ := -188847/125000) 280 160
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t36 : ((763035528119/5000000000000 : ℚ) : ℝ) ≤ stT280 36 := by
  have hc : ((915643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((763035528119/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((915643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c37 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((112239/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2437419/10000000) (δ := 14057/1000000000) (ψ := -188847/125000) 280 161
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t37 : ((184503241481/2000000000000 : ℚ) : ℝ) ≤ stT280 37 := by
  have hc : ((112229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184503241481/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((112229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c38 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-277383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1349299/2500000) (δ := 2833/200000000) (ψ := -188847/125000) 280 162
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t38 : ((-2812596367/31250000000 : ℚ) : ℝ) ≤ stT280 38 := by
  have hc : ((-8669/15625 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2812596367/31250000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-8669/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c39 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-499987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7835881/10000000) (δ := 1753/125000000) (ψ := -188847/125000) 280 164
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t39 : ((-100082526923/625000000000 : ℚ) : ℝ) ≤ stT280 39 := by
  have hc : ((-125003/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100082526923/625000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-125003/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c40 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-343647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727673/1250000) (δ := 7043/500000000) (ψ := -188847/125000) 280 165
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t40 : ((-67924150301/625000000000 : ℚ) : ℝ) ≤ stT280 40 := by
  have hc : ((-42959/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67924150301/625000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-42959/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c41 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-126673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4244527/10000000) (δ := 14193/1000000000) (ψ := -188847/125000) 280 166
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t41 : ((-98954062287/5000000000000 : ℚ) : ℝ) ≤ stT280 41 := by
  have hc : ((-126723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98954062287/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-126723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c42 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((165389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3084171/10000000) (δ := 14103/1000000000) (ψ := -188847/125000) 280 167
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t42 : ((63790527253/1250000000000 : ℚ) : ℝ) ≤ stT280 42 := by
  have hc : ((41341/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63790527253/1250000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((41341/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c43 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((119837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145049/625000) (δ := 1751/125000000) (ψ := -188847/125000) 280 168
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t43 : ((36546875519/400000000000 : ℚ) : ℝ) ≤ stT280 43 := by
  have hc : ((119827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36546875519/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((119827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c44 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((357407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936097/10000000) (δ := 2823/200000000) (ψ := -188847/125000) 280 169
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t44 : ((67346672299/625000000000 : ℚ) : ℝ) ≤ stT280 44 := by
  have hc : ((178691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67346672299/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((178691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c45 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((11269/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1913101/10000000) (δ := 14181/1000000000) (ψ := -188847/125000) 280 170
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t45 : ((537525044513/5000000000000 : ℚ) : ℝ) ≤ stT280 45 := by
  have hc : ((360583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537525044513/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((360583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c46 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((626039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1117917/5000000) (δ := 7037/500000000) (ψ := -188847/125000) 280 171
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t46 : ((922970075391/10000000000000 : ℚ) : ℝ) ≤ stT280 46 := by
  have hc : ((625989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((922970075391/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((625989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c47 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((100807/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2889387/10000000) (δ := 3509/250000000) (ψ := -188847/125000) 280 172
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t47 : ((294047593261/5000000000000 : ℚ) : ℝ) ≤ stT280 47 := by
  have hc : ((201589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294047593261/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((201589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c48 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((5361/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -385997/1000000) (δ := 221/15625000) (ψ := -188847/125000) 280 173
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t48 : ((61787997/16000000000 : ℚ) : ℝ) ≤ stT280 48 := by
  have hc : ((5351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61787997/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((5351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c49 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-464439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2567247/5000000) (δ := 1769/125000000) (ψ := -188847/125000) 280 174
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t49 : ((-165888994927/2500000000000 : ℚ) : ℝ) ≤ stT280 49 := by
  have hc : ((-464489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165888994927/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-464489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c50 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-895433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6700497/10000000) (δ := 2809/200000000) (ψ := -188847/125000) 280 175
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t50 : ((-633202297681/5000000000000 : ℚ) : ℝ) ≤ stT280 50 := by
  have hc : ((-895483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-633202297681/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-895483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c51 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-961863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7161323/10000000) (δ := 2809/200000000) (ψ := -188847/125000) 280 175
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t51 : ((-1346948497553/10000000000000 : ℚ) : ℝ) ≤ stT280 51 := by
  have hc : ((-961913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1346948497553/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-961913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c52 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-432817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504603/1000000) (δ := 2813/200000000) (ψ := -188847/125000) 280 176
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t52 : ((-600278745117/10000000000000 : ℚ) : ℝ) ≤ stT280 52 := by
  have hc : ((-432867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-600278745117/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-432867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c53 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((120311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2671807/10000000) (δ := 3543/250000000) (ψ := -188847/125000) 280 177
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t53 : ((66097048437/1000000000000 : ℚ) : ℝ) ≤ stT280 53 := by
  have hc : ((240597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66097048437/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((240597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c54 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((999813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48313/10000000) (δ := 3531/250000000) (ψ := -188847/125000) 280 178
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t54 : ((1360504484001/10000000000000 : ℚ) : ℝ) ≤ stT280 54 := by
  have hc : ((999763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1360504484001/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((999763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c55 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((430173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35191/125000) (δ := 219/15625000) (ψ := -188847/125000) 280 179
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t55 : ((579977423077/10000000000000 : ℚ) : ℝ) ≤ stT280 55 := by
  have hc : ((430123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((579977423077/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((430123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c56 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-712687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5910293/10000000) (δ := 7047/500000000) (ψ := -188847/125000) 280 180
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t56 : ((-952435442259/10000000000000 : ℚ) : ℝ) ≤ stT280 56 := by
  have hc : ((-712737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-952435442259/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-712737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c57 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-426309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6479427/10000000) (δ := 7047/500000000) (ψ := -188847/125000) 280 180
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t57 : ((-282346726011/2500000000000 : ℚ) : ℝ) ≤ stT280 57 := by
  have hc : ((-213167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282346726011/2500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-213167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c58 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((191253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 736431/2500000) (δ := 14201/1000000000) (ψ := -188847/125000) 280 181
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t58 : ((7846706331/156250000000 : ℚ) : ℝ) ≤ stT280 58 := by
  have hc : ((47807/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7846706331/156250000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((47807/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c59 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((949717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1244/15625) (δ := 2819/200000000) (ψ := -188847/125000) 280 182
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t59 : ((1236361020963/10000000000000 : ℚ) : ℝ) ≤ stT280 59 := by
  have hc : ((949667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1236361020963/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((949667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c60 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-319181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4739153/10000000) (δ := 2803/200000000) (ψ := -188847/125000) 280 183
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t60 : ((-82425124969/2000000000000 : ℚ) : ℝ) ≤ stT280 60 := by
  have hc : ((-319231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82425124969/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-319231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c61 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-917499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6831357/10000000) (δ := 2803/200000000) (ψ := -188847/125000) 280 183
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t61 : ((-1174801295581/10000000000000 : ℚ) : ℝ) ≤ stT280 61 := by
  have hc : ((-917549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1174801295581/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-917549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c62 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((8412/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156609/625000) (δ := 14123/1000000000) (ψ := -188847/125000) 280 184
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t62 : ((341832199159/5000000000000 : ℚ) : ℝ) ≤ stT280 62 := by
  have hc : ((269159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341832199159/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((269159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c63 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((13923/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100097/500000) (δ := 14173/1000000000) (ψ := -188847/125000) 280 185
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t63 : ((8770031641/100000000000 : ℚ) : ℝ) ≤ stT280 63 := by
  have hc : ((6961/10000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8770031641/100000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((6961/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c64 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-892853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6686093/10000000) (δ := 7033/500000000) (ψ := -188847/125000) 280 186
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t64 : ((-1116129642903/10000000000000 : ℚ) : ℝ) ≤ stT280 64 := by
  have hc : ((-892903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1116129642903/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-892903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c65 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-19159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4166847/10000000) (δ := 7033/500000000) (ψ := -188847/125000) 280 186
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t65 : ((-5944057703/500000000000 : ℚ) : ℝ) ≤ stT280 65 := by
  have hc : ((-19169/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5944057703/500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-19169/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c66 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((471119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426933/5000000) (δ := 3511/250000000) (ψ := -188847/125000) 280 187
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t66 : ((144969049979/1250000000000 : ℚ) : ℝ) ≤ stT280 66 := by
  have hc : ((235547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144969049979/1250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((235547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c67 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-746857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6035299/10000000) (δ := 14151/1000000000) (ψ := -188847/125000) 280 188
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t67 : ((-182498509473/2000000000000 : ℚ) : ℝ) ≤ stT280 67 := by
  have hc : ((-746907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182498509473/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-746907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c68 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-162587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4335271/10000000) (δ := 14151/1000000000) (ψ := -188847/125000) 280 188
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t68 : ((-197226474523/10000000000000 : ℚ) : ℝ) ≤ stT280 68 := by
  have hc : ((-162637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197226474523/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-162637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c69 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((13991/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153533/10000000) (δ := 2829/200000000) (ψ := -188847/125000) 280 189
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t69 : ((269475788223/2500000000000 : ℚ) : ℝ) ≤ stT280 69 := by
  have hc : ((447687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269475788223/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((447687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c70 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-113837/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3394703/5000000) (δ := 14037/1000000000) (ψ := -188847/125000) 280 190
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t70 : ((-544275015417/5000000000000 : ℚ) : ℝ) ≤ stT280 70 := by
  have hc : ((-455373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544275015417/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-455373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c71 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((154847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1569907/5000000) (δ := 14037/1000000000) (ψ := -188847/125000) 280 190
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t71 : ((91869903991/2500000000000 : ℚ) : ℝ) ≤ stT280 71 := by
  have hc : ((77411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91869903991/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((77411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c72 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((2773/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2777739/10000000) (δ := 14073/1000000000) (ψ := -188847/125000) 280 191
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t72 : ((52282283493/1000000000000 : ℚ) : ℝ) ≤ stT280 72 := by
  have hc : ((44363/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52282283493/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((44363/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c73 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-462347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6877571/10000000) (δ := 14073/1000000000) (ψ := -188847/125000) 280 191
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t73 : ((-33822858579/312500000000 : ℚ) : ℝ) ≤ stT280 73 := by
  have hc : ((-115593/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33822858579/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-115593/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c74 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((120221/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86691/1250000) (δ := 709/50000000) (ψ := -188847/125000) 280 192
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t74 : ((139746761721/1250000000000 : ℚ) : ℝ) ≤ stT280 74 := by
  have hc : ((480859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139746761721/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((480859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c75 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-156519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2809133/5000000) (δ := 3529/250000000) (ψ := -188847/125000) 280 193
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t75 : ((-361494159163/5000000000000 : ℚ) : ℝ) ≤ stT280 75 := by
  have hc : ((-313063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361494159163/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-313063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c76 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((27307/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1826687/5000000) (δ := 3529/250000000) (ψ := -188847/125000) 280 193
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t76 : ((31308920471/2500000000000 : ℚ) : ℝ) ≤ stT280 76 := by
  have hc : ((54589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31308920471/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((54589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c77 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((99457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2904119/10000000) (δ := 14009/1000000000) (ψ := -188847/125000) 280 194
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t77 : ((45330979769/1000000000000 : ℚ) : ℝ) ≤ stT280 77 := by
  have hc : ((198889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45330979769/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((198889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c78 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-385531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6128261/10000000) (δ := 14009/1000000000) (ψ := -188847/125000) 280 194
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t78 : ((-54569572071/625000000000 : ℚ) : ℝ) ≤ stT280 78 := by
  have hc : ((-96389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54569572071/625000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-96389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c79 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((965103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -331201/5000000) (δ := 7051/500000000) (ψ := -188847/125000) 280 195
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t79 : ((1085768584611/10000000000000 : ℚ) : ℝ) ≤ stT280 79 := by
  have hc : ((965053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1085768584611/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((965053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c80 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-124167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3782603/5000000) (δ := 7097/500000000) (ψ := -188847/125000) 280 196
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t80 : ((-277659830781/2500000000000 : ℚ) : ℝ) ≤ stT280 80 := by
  have hc : ((-496693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277659830781/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-496693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c81 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((22487/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70659/625000) (δ := 7097/500000000) (ψ := -188847/125000) 280 196
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t81 : ((99936656673/1000000000000 : ℚ) : ℝ) ≤ stT280 81 := by
  have hc : ((89943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99936656673/1000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((89943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c82 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-367119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5988349/10000000) (δ := 14087/1000000000) (ψ := -188847/125000) 280 197
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t82 : ((-12670093547/156250000000 : ℚ) : ℝ) ≤ stT280 82 := by
  have hc : ((-45893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12670093547/156250000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-45893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c83 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((135359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2496631/10000000) (δ := 14087/1000000000) (ψ := -188847/125000) 280 197
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t83 : ((148562002953/2500000000000 : ℚ) : ℝ) ≤ stT280 83 := by
  have hc : ((270693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148562002953/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((270693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c84 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-176331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4828027/10000000) (δ := 28023/1000000000) (ψ := -188847/125000) 280 198
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t84 : ((-4810506701/125000000000 : ℚ) : ℝ) ≤ stT280 84 := by
  have hc : ((-44089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4810506701/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-44089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c85 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((187249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432011/1250000) (δ := 14023/1000000000) (ψ := -188847/125000) 280 198
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t85 : ((50761442437/2500000000000 : ℚ) : ℝ) ≤ stT280 85 := by
  have hc : ((187199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50761442437/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((187199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c86 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-27523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162587/400000) (δ := 1413/100000000) (ψ := -188847/125000) 280 199
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t86 : ((-928305617/156250000000 : ℚ) : ℝ) ≤ stT280 86 := by
  have hc : ((-6887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-928305617/156250000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-6887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c87 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-323/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 805591/2000000) (δ := 1413/100000000) (ψ := -188847/125000) 280 199
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t87 : ((-1733606721/400000000000 : ℚ) : ℝ) ≤ stT280 87 := by
  have hc : ((-1617/40000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1733606721/400000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-1617/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c88 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((24667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3679919/10000000) (δ := 7083/500000000) (ψ := -188847/125000) 280 200
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t88 : ((52563541927/5000000000000 : ℚ) : ℝ) ≤ stT280 88 := by
  have hc : ((49309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52563541927/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((49309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c89 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-151/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4229731/10000000) (δ := 7083/500000000) (ψ := -188847/125000) 280 200
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t89 : ((-1281007583/100000000000 : ℚ) : ℝ) ≤ stT280 89 := by
  have hc : ((-2417/20000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1281007583/100000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-2417/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c90 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((53909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1828461/5000000) (δ := 7029/500000000) (ψ := -188847/125000) 280 201
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t90 : ((3549918333/312500000000 : ℚ) : ℝ) ≤ stT280 90 := by
  have hc : ((13471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3549918333/312500000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((13471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c91 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-15089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4077973/10000000) (δ := 14029/500000000) (ψ := -188847/125000) 280 201
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t91 : ((-6332270371/1000000000000 : ℚ) : ℝ) ≤ stT280 91 := by
  have hc : ((-30203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6332270371/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-30203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c92 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-2633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -795931/2000000) (δ := 3513/250000000) (ψ := -188847/125000) 280 202
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t92 : ((-11006443161/5000000000000 : ℚ) : ℝ) ≤ stT280 92 := by
  have hc : ((-10557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11006443161/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-10557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c93 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((135191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143519/400000) (δ := 3513/250000000) (ψ := -188847/125000) 280 202
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t93 : ((140134595091/10000000000000 : ℚ) : ℝ) ≤ stT280 93 := by
  have hc : ((135141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140134595091/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((135141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c94 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-69693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2316639/5000000) (δ := 14159/1000000000) (ψ := -188847/125000) 280 203
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t94 : ((-71895786221/2500000000000 : ℚ) : ℝ) ≤ stT280 94 := by
  have hc : ((-139411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71895786221/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-139411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c95 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((444951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173387/625000) (δ := 14159/1000000000) (ψ := -188847/125000) 280 203
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t95 : ((228229319089/5000000000000 : ℚ) : ℝ) ≤ stT280 95 := by
  have hc : ((444901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228229319089/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((444901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c96 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-155393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2801931/5000000) (δ := 14137/1000000000) (ψ := -188847/125000) 280 204
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t96 : ((-317220233631/5000000000000 : ℚ) : ℝ) ≤ stT280 96 := by
  have hc : ((-310811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317220233631/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-310811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c97 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((49373/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 825049/5000000) (δ := 14137/1000000000) (ψ := -188847/125000) 280 204
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t97 : ((200510020407/2500000000000 : ℚ) : ℝ) ≤ stT280 97 := by
  have hc : ((394959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200510020407/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((394959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c98 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-115601/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1375663/2000000) (δ := 1403/100000000) (ψ := -188847/125000) 280 205
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t98 : ((-467124041637/5000000000000 : ℚ) : ℝ) ≤ stT280 98 := by
  have hc : ((-462429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467124041637/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-462429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c99 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((995831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45673/2000000) (δ := 1403/100000000) (ψ := -188847/125000) 280 205
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t99 : ((1000796748897/10000000000000 : ℚ) : ℝ) ≤ stT280 99 := by
  have hc : ((995781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1000796748897/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((995781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c100 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-972243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290543/400000) (δ := 1403/100000000) (ψ := -188847/125000) 280 205
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t100 : ((-972293/10000000 : ℚ) : ℝ) ≤ stT280 100 := by
  have hc : ((-972293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-972293/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-972293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c101 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((33201/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -369777/2500000) (δ := 11/781250) (ψ := -188847/125000) 280 206
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t101 : ((33034233363/400000000000 : ℚ) : ℝ) ≤ stT280 101 := by
  have hc : ((33199/40000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33034233363/400000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((33199/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c102 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-280753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2708751/5000000) (δ := 11/781250) (ψ := -188847/125000) 280 206
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t102 : ((-34751471893/625000000000 : ℚ) : ℝ) ≤ stT280 102 := by
  have hc : ((-140389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34751471893/625000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-140389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c103 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((46311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3461191/10000000) (δ := 3547/250000000) (ψ := -188847/125000) 280 207
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t103 : ((91238509413/5000000000000 : ℚ) : ℝ) ≤ stT280 103 := by
  have hc : ((92597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91238509413/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((92597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c104 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((247347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3302139/10000000) (δ := 3547/250000000) (ψ := -188847/125000) 280 207
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t104 : ((12124724613/500000000000 : ℚ) : ℝ) ≤ stT280 104 := by
  have hc : ((247297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12124724613/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((247297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c105 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-130681/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228287/400000) (δ := 3527/250000000) (ψ := -188847/125000) 280 208
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t105 : ((-127541477591/2000000000000 : ℚ) : ℝ) ≤ stT280 105 := by
  have hc : ((-130691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127541477591/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-130691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c106 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((186381/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185583/2000000) (δ := 3527/250000000) (ψ := -188847/125000) 280 208
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t106 : ((36203871347/400000000000 : ℚ) : ℝ) ≤ stT280 106 := by
  have hc : ((186371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36203871347/400000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((186371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c107 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-247509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 300031/400000) (δ := 3527/250000000) (ψ := -188847/125000) 280 208
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t107 : ((-478576384691/5000000000000 : ℚ) : ℝ) ≤ stT280 107 := by
  have hc : ((-495043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-478576384691/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-495043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c108 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((778701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -423877/2500000) (δ := 7001/500000000) (ψ := -188847/125000) 280 209
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t108 : ((2997027699/40000000000 : ℚ) : ℝ) ≤ stT280 108 := by
  have hc : ((778651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2997027699/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((778651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c109 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-162801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297257/625000) (δ := 7001/500000000) (ψ := -188847/125000) 280 209
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t109 : ((-77979569551/2500000000000 : ℚ) : ℝ) ≤ stT280 109 := by
  have hc : ((-81413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77979569551/2500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-81413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c110 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-250159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4559101/10000000) (δ := 14109/1000000000) (ψ := -188847/125000) 280 210
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t110 : ((-238565023767/10000000000000 : ℚ) : ℝ) ≤ stT280 110 := by
  have hc : ((-250209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238565023767/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-250209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c111 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((379073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1775829/10000000) (δ := 14109/1000000000) (ψ := -188847/125000) 280 210
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t111 : ((44972007817/625000000000 : ℚ) : ℝ) ≤ stT280 111 := by
  have hc : ((47381/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44972007817/625000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((47381/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c112 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-498403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1530823/2000000) (δ := 14187/1000000000) (ψ := -188847/125000) 280 211
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t112 : ((-7358915599/78125000000 : ℚ) : ℝ) ≤ stT280 112 := by
  have hc : ((-124607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7358915599/78125000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-124607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c113 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((840427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -286363/2000000) (δ := 14187/1000000000) (ψ := -188847/125000) 280 211
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t113 : ((9881993143/125000000000 : ℚ) : ℝ) ≤ stT280 113 := by
  have hc : ((840377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9881993143/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((840377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c114 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-63567/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947121/2000000) (δ := 14187/1000000000) (ψ := -188847/125000) 280 211
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t114 : ((-29772664061/1000000000000 : ℚ) : ℝ) ≤ stT280 114 := by
  have hc : ((-63577/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29772664061/1000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-63577/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c115 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-182071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303673/625000) (δ := 14079/1000000000) (ψ := -188847/125000) 280 212
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t115 : ((-2122567881/62500000000 : ℚ) : ℝ) ≤ stT280 115 := by
  have hc : ((-11381/31250 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2122567881/62500000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-11381/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c116 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((13854/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150229/1250000) (δ := 14079/1000000000) (ψ := -188847/125000) 280 212
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t116 : ((102899049057/1250000000000 : ℚ) : ℝ) ≤ stT280 116 := by
  have hc : ((443303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102899049057/1250000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((443303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c117 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-60441/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1802623/2500000) (δ := 14079/1000000000) (ψ := -188847/125000) 280 212
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t117 : ((-447045232053/5000000000000 : ℚ) : ℝ) ≤ stT280 117 := by
  have hc : ((-483553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-447045232053/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-483553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c118 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((526777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2539981/10000000) (δ := 14031/1000000000) (ψ := -188847/125000) 280 213
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t118 : ((242445590649/5000000000000 : ℚ) : ℝ) ≤ stT280 118 := by
  have hc : ((526727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242445590649/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((526727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c119 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((111029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3367179/10000000) (δ := 14031/1000000000) (ψ := -188847/125000) 280 213
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t119 : ((12719643099/625000000000 : ℚ) : ℝ) ≤ stT280 119 := by
  have hc : ((27751/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12719643099/625000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((27751/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c120 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-426679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3241487/5000000) (δ := 7069/500000000) (ψ := -188847/125000) 280 214
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t120 : ((-24345356699/312500000000 : ℚ) : ℝ) ≤ stT280 120 := by
  have hc : ((-26669/31250 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24345356699/312500000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-26669/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c121 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((963897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336907/5000000) (δ := 7069/500000000) (ψ := -188847/125000) 280 214
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t121 : ((87622366923/1000000000000 : ℚ) : ℝ) ≤ stT280 121 := by
  have hc : ((963847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87622366923/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((963847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c122 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-111931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317971/625000) (δ := 7069/500000000) (ψ := -188847/125000) 280 214
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t122 : ((-101348943273/2500000000000 : ℚ) : ℝ) ≤ stT280 122 := by
  have hc : ((-223887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101348943273/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-223887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c123 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-76343/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2453059/5000000) (δ := 7079/500000000) (ψ := -188847/125000) 280 215
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t123 : ((-6884520951/200000000000 : ℚ) : ℝ) ≤ stT280 123 := by
  have hc : ((-76353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6884520951/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-76353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c124 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((238479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 380961/5000000) (δ := 7079/500000000) (ψ := -188847/125000) 280 215
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t124 : ((214149117129/2500000000000 : ℚ) : ℝ) ≤ stT280 124 := by
  have hc : ((476933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214149117129/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((476933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c125 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-416079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3192231/5000000) (δ := 7079/500000000) (ψ := -188847/125000) 280 215
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t125 : ((-11630470891/156250000000 : ℚ) : ℝ) ≤ stT280 125 := by
  have hc : ((-52013/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11630470891/156250000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-52013/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c126 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((18107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3745761/10000000) (δ := 14051/1000000000) (ψ := -188847/125000) 280 216
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t126 : ((3223969443/500000000000 : ℚ) : ℝ) ≤ stT280 126 := by
  have hc : ((36189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3223969443/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((36189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c127 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((188753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1787809/10000000) (δ := 14051/1000000000) (ψ := -188847/125000) 280 216
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t127 : ((83740007559/1250000000000 : ℚ) : ℝ) ≤ stT280 127 := by
  have hc : ((377481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83740007559/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((377481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c128 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-973581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7278049/10000000) (δ := 14051/1000000000) (ψ := -188847/125000) 280 216
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t128 : ((-215144215701/2500000000000 : ℚ) : ℝ) ≤ stT280 128 := by
  have hc : ((-973631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215144215701/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-973631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c129 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((9223/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1491187/5000000) (δ := 14059/1000000000) (ψ := -188847/125000) 280 217
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t129 : ((649543183/20000000000 : ℚ) : ℝ) ≤ stT280 129 := by
  have hc : ((36887/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((649543183/20000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((36887/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c130 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((565951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1211513/5000000) (δ := 14059/1000000000) (ψ := -188847/125000) 280 217
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t130 : ((248163999629/5000000000000 : ℚ) : ℝ) ≤ stT280 130 := by
  have hc : ((565901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248163999629/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((565901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c131 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-499821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 486691/625000) (δ := 14059/1000000000) (ψ := -188847/125000) 280 217
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t131 : ((-43671794943/500000000000 : ℚ) : ℝ) ≤ stT280 131 := by
  have hc : ((-249923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43671794943/500000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-249923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c132 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((253509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2597687/10000000) (δ := 14167/1000000000) (ψ := -188847/125000) 280 218
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t132 : ((13789339487/312500000000 : ℚ) : ℝ) ≤ stT280 132 := by
  have hc : ((63371/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13789339487/312500000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((63371/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c133 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((476487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2685353/10000000) (δ := 14167/1000000000) (ψ := -188847/125000) 280 218
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t133 : ((413122810633/10000000000000 : ℚ) : ℝ) ≤ stT280 133 := by
  have hc : ((476437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((413122810633/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((476437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c134 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-15618/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1944789/2500000) (δ := 28129/1000000000) (ψ := -188847/125000) 280 219
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t134 : ((-431762590069/5000000000000 : ℚ) : ℝ) ≤ stT280 134 := by
  have hc : ((-499801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431762590069/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-499801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c135 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((20597/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2574691/10000000) (δ := 14129/1000000000) (ψ := -188847/125000) 280 219
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t135 : ((1772533389/40000000000 : ℚ) : ℝ) ≤ stT280 135 := by
  have hc : ((4119/8000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1772533389/40000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((4119/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c136 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((509191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2591379/10000000) (δ := 14129/1000000000) (ψ := -188847/125000) 280 219
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t136 : ((109146083593/2500000000000 : ℚ) : ℝ) ≤ stT280 136 := by
  have hc : ((509141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109146083593/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((509141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c137 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-998557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7719649/10000000) (δ := 14129/1000000000) (ψ := -188847/125000) 280 219
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t137 : ((-426583939653/5000000000000 : ℚ) : ℝ) ≤ stT280 137 := by
  have hc : ((-998607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426583939653/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-998607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c138 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((100071/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181089/625000) (δ := 7011/500000000) (ψ := -188847/125000) 280 220
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t138 : ((21293849619/625000000000 : ℚ) : ℝ) ≤ stT280 138 := by
  have hc : ((200117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21293849619/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((200117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c139 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((325189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1078393/5000000) (δ := 7011/500000000) (ψ := -188847/125000) 280 220
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t139 : ((17237512677/312500000000 : ℚ) : ℝ) ≤ stT280 139 := by
  have hc : ((81291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17237512677/312500000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((81291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c140 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-963317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448421/625000) (δ := 7011/500000000) (ψ := -188847/125000) 280 220
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t140 : ((-162838887377/2000000000000 : ℚ) : ℝ) ≤ stT280 140 := by
  have hc : ((-963367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162838887377/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-963367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c141 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((149811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3551047/10000000) (δ := 1761/125000000) (ψ := -188847/125000) 280 221
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t141 : ((126121375911/10000000000000 : ℚ) : ℝ) ≤ stT280 141 := by
  have hc : ((149761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126121375911/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((149761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c142 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((169621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1395993/10000000) (δ := 1761/125000000) (ψ := -188847/125000) 280 221
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t142 : ((142334328591/2000000000000 : ℚ) : ℝ) ≤ stT280 142 := by
  have hc : ((169611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142334328591/2000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((169611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c143 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-203721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6308313/10000000) (δ := 1761/125000000) (ψ := -188847/125000) 280 221
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t143 : ((-340741426481/5000000000000 : ℚ) : ℝ) ≤ stT280 143 := by
  have hc : ((-407467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340741426481/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-407467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c144 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-235619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452163/1000000) (δ := 2839/200000000) (ψ := -188847/125000) 280 222
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t144 : ((-98195495223/5000000000000 : ℚ) : ℝ) ≤ stT280 144 := by
  have hc : ((-235669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98195495223/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-235669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c145 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((3099/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2017/62500) (δ := 2839/200000000) (ψ := -188847/125000) 280 222
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t145 : ((41175155001/500000000000 : ℚ) : ℝ) ≤ stT280 145 := by
  have hc : ((99163/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41175155001/500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((99163/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c146 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-29011/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4107/8000) (δ := 2839/200000000) (ψ := -188847/125000) 280 222
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t146 : ((-96049055739/2500000000000 : ℚ) : ℝ) ≤ stT280 146 := by
  have hc : ((-232113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96049055739/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-232113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c147 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-169977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449021/2500000) (δ := 141/10000000) (ψ := -188847/125000) 280 223
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t147 : ((-280410259473/5000000000000 : ℚ) : ℝ) ≤ stT280 147 := by
  have hc : ((-339979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280410259473/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-339979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c148 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((913041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525147/5000000) (δ := 141/10000000) (ψ := -188847/125000) 280 223
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t148 : ((375236562027/5000000000000 : ℚ) : ℝ) ≤ stT280 148 := by
  have hc : ((912991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375236562027/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((912991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c149 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((105171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 457947/1250000) (δ := 141/10000000) (ψ := -188847/125000) 280 223
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t149 : ((86118381951/10000000000000 : ℚ) : ℝ) ≤ stT280 149 := by
  have hc : ((105121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86118381951/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((105121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c150 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-980711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7362157/10000000) (δ := 1401/100000000) (ψ := -188847/125000) 280 224
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t150 : ((-800788414217/10000000000000 : ℚ) : ℝ) ≤ stT280 150 := by
  have hc : ((-980761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-800788414217/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-980761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c151 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((93493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2710937/10000000) (δ := 1401/100000000) (ψ := -188847/125000) 280 224
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t151 : ((19018835901/500000000000 : ℚ) : ℝ) ≤ stT280 151 := by
  have hc : ((93483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19018835901/500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((93483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c152 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((361099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909553/10000000) (δ := 1401/100000000) (ψ := -188847/125000) 280 224
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t152 : ((146434824459/2500000000000 : ℚ) : ℝ) ≤ stT280 152 := by
  have hc : ((180537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146434824459/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((180537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c153 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-428417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6499733/10000000) (δ := 1401/100000000) (ψ := -188847/125000) 280 224
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t153 : ((-173187610113/2500000000000 : ℚ) : ℝ) ≤ stT280 153 := by
  have hc : ((-214221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173187610113/2500000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-214221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c154 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-284399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232397/500000) (δ := 14117/1000000000) (ψ := -188847/125000) 280 225
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t154 : ((-229215546527/10000000000000 : ℚ) : ℝ) ≤ stT280 154 := by
  have hc : ((-284449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229215546527/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-284449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c155 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((499451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11719/1000000) (δ := 14117/1000000000) (ψ := -188847/125000) 280 225
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t155 : ((200574226147/2500000000000 : ℚ) : ℝ) ≤ stT280 155 := by
  have hc : ((249713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200574226147/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((249713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c156 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-4549/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109611/250000) (δ := 14117/1000000000) (ψ := -188847/125000) 280 225
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t156 : ((-14572466841/1000000000000 : ℚ) : ℝ) ≤ stT280 156 := by
  have hc : ((-18201/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14572466841/1000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-18201/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c157 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-920543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856333/1250000) (δ := 14179/1000000000) (ψ := -188847/125000) 280 226
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t157 : ((-734713305591/10000000000000 : ℚ) : ℝ) ≤ stT280 157 := by
  have hc : ((-920593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-734713305591/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-920593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c158 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((571479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150389/625000) (δ := 14179/1000000000) (ψ := -188847/125000) 280 226
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t158 : ((454604340953/10000000000000 : ℚ) : ℝ) ≤ stT280 158 := by
  have hc : ((571429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454604340953/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((571429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c159 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((693769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251277/1250000) (δ := 14179/1000000000) (ψ := -188847/125000) 280 226
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t159 : ((550154546669/10000000000000 : ℚ) : ℝ) ≤ stT280 159 := by
  have hc : ((693719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((550154546669/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((693719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c160 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-167071/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 799867/1250000) (δ := 14179/1000000000) (ψ := -188847/125000) 280 226
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t160 : ((-13208922617/200000000000 : ℚ) : ℝ) ≤ stT280 160 := by
  have hc : ((-167081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13208922617/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-167081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c161 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-198513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4947677/10000000) (δ := 1759/125000000) (ψ := -188847/125000) 280 227
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t161 : ((-78234990859/2500000000000 : ℚ) : ℝ) ≤ stT280 161 := by
  have hc : ((-99269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78234990859/2500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-99269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c162 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((485031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -613277/10000000) (δ := 1759/125000000) (ψ := -188847/125000) 280 227
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t162 : ((95264151011/1250000000000 : ℚ) : ℝ) ≤ stT280 162 := by
  have hc : ((242503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95264151011/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((242503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c163 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((92881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3694453/10000000) (δ := 1759/125000000) (ψ := -188847/125000) 280 227
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t163 : ((3635540453/500000000000 : ℚ) : ℝ) ≤ stT280 163 := by
  have hc : ((92831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3635540453/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((92831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c164 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-998813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -773217/1000000) (δ := 7019/500000000) (ψ := -188847/125000) 280 228
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t164 : ((-779981151947/10000000000000 : ℚ) : ℝ) ≤ stT280 164 := by
  have hc : ((-998863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-779981151947/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-998863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c165 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((179077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347687/1000000) (δ := 7019/500000000) (ψ := -188847/125000) 280 228
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t165 : ((69686080723/5000000000000 : ℚ) : ℝ) ≤ stT280 165 := by
  have hc : ((179027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69686080723/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((179027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c166 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((238753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37637/500000) (δ := 7019/500000000) (ψ := -188847/125000) 280 228
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t166 : ((7411937563/100000000000 : ℚ) : ℝ) ≤ stT280 166 := by
  have hc : ((477481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7411937563/100000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((477481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c167 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-8009/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 495701/1000000) (δ := 7019/500000000) (ψ := -188847/125000) 280 228
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t167 : ((-9684891/312500000 : ℚ) : ℝ) ≤ stT280 167 := by
  have hc : ((-801/2000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9684891/312500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-801/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c168 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-174271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6571883/10000000) (δ := 7073/500000000) (ψ := -188847/125000) 280 229
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t168 : ((-134460754277/2000000000000 : ℚ) : ℝ) ≤ stT280 168 := by
  have hc : ((-174281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134460754277/2000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-174281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c169 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((141941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2417523/10000000) (δ := 7073/500000000) (ψ := -188847/125000) 280 229
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t169 : ((21835132011/500000000000 : ℚ) : ℝ) ≤ stT280 169 := by
  have hc : ((283857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21835132011/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((283857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c170 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((387239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1712267/10000000) (δ := 7073/500000000) (ψ := -188847/125000) 280 229
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t170 : ((37122399787/625000000000 : ℚ) : ℝ) ≤ stT280 170 := by
  have hc : ((193607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37122399787/625000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((193607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c171 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-686263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5817837/10000000) (δ := 7073/500000000) (ψ := -188847/125000) 280 229
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t171 : ((-6560465967/125000000000 : ℚ) : ℝ) ≤ stT280 171 := by
  have hc : ((-686313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6560465967/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-686313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c172 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-683541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5808497/10000000) (δ := 283/20000000) (ψ := -188847/125000) 280 230
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t172 : ((-521233352363/10000000000000 : ℚ) : ℝ) ≤ stT280 172 := by
  have hc : ((-683591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521233352363/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-683591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c173 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((382353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1750527/10000000) (δ := 283/20000000) (ψ := -188847/125000) 280 230
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t173 : ((7266956087/125000000000 : ℚ) : ℝ) ≤ stT280 173 := by
  have hc : ((47791/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7266956087/125000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((47791/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c174 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((1909/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2284063/10000000) (δ := 283/20000000) (ψ := -188847/125000) 280 230
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t174 : ((23153450067/500000000000 : ℚ) : ℝ) ≤ stT280 174 := by
  have hc : ((61083/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23153450067/500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((61083/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c175 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-162383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6295553/10000000) (δ := 283/20000000) (ψ := -188847/125000) 280 230
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t175 : ((-122757578097/2000000000000 : ℚ) : ℝ) ≤ stT280 175 := by
  have hc : ((-162393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122757578097/2000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-162393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c176 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-70449/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -542381/1000000) (δ := 14043/1000000000) (ψ := -188847/125000) 280 231
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t176 : ((-212430751559/5000000000000 : ℚ) : ℝ) ≤ stT280 176 := by
  have hc : ((-281821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212430751559/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-281821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c177 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((20869/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5831/40000) (δ := 14043/1000000000) (ψ := -188847/125000) 280 231
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t177 : ((31370321633/500000000000 : ℚ) : ℝ) ≤ stT280 177 := by
  have hc : ((83471/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31370321633/500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((83471/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c178 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((136259/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248591/1000000) (δ := 14043/1000000000) (ψ := -188847/125000) 280 231
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t178 : ((204241950783/5000000000000 : ℚ) : ℝ) ≤ stT280 178 := by
  have hc : ((272493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204241950783/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((272493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c179 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-837237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40047/62500) (δ := 14043/1000000000) (ψ := -188847/125000) 280 231
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t179 : ((-156454611533/2500000000000 : ℚ) : ℝ) ≤ stT280 179 := by
  have hc : ((-837287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156454611533/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-837287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c180 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-277973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5400743/10000000) (δ := 14067/1000000000) (ψ := -188847/125000) 280 232
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t180 : ((-25900934661/625000000000 : ℚ) : ℝ) ≤ stT280 180 := by
  have hc : ((-138999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25900934661/625000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-138999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c181 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((820197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1522603/10000000) (δ := 14067/1000000000) (ψ := -188847/125000) 280 232
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t181 : ((304805172109/5000000000000 : ℚ) : ℝ) ≤ stT280 181 := by
  have hc : ((820147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304805172109/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((820147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c182 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((594907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2334117/10000000) (δ := 14067/1000000000) (ψ := -188847/125000) 280 232
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t182 : ((440937156393/10000000000000 : ℚ) : ℝ) ≤ stT280 182 := by
  have hc : ((594857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440937156393/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((594857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c183 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-781527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6169767/10000000) (δ := 14067/1000000000) (ψ := -188847/125000) 280 232
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t183 : ((-288879456547/5000000000000 : ℚ) : ℝ) ≤ stT280 183 := by
  have hc : ((-781577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288879456547/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-781577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c184 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-658327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1430869/2500000) (δ := 7087/500000000) (ψ := -188847/125000) 280 233
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t184 : ((-48536210817/1000000000000 : ℚ) : ℝ) ≤ stT280 184 := by
  have hc : ((-658377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48536210817/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-658377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c185 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((716683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964703/5000000) (δ := 7087/500000000) (ψ := -188847/125000) 280 233
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t185 : ((263439307231/5000000000000 : ℚ) : ℝ) ≤ stT280 185 := by
  have hc : ((716633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263439307231/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((716633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c186 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((740043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 922077/5000000) (δ := 7087/500000000) (ψ := -188847/125000) 280 233
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t186 : ((108517753471/2000000000000 : ℚ) : ℝ) ≤ stT280 186 := by
  have hc : ((739993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108517753471/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((739993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c187 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-309797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2798777/5000000) (δ := 7087/500000000) (ψ := -188847/125000) 280 233
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t187 : ((-113282231703/2500000000000 : ℚ) : ℝ) ≤ stT280 187 := by
  have hc : ((-154911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113282231703/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-154911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c188 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-415261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63771/100000) (δ := 14121/1000000000) (ψ := -188847/125000) 280 234
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t188 : ((-6057569239/100000000000 : ℚ) : ℝ) ≤ stT280 188 := by
  have hc : ((-207643/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6057569239/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-207643/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c189 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((30259/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266353/1000000) (δ := 14121/1000000000) (ψ := -188847/125000) 280 234
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t189 : ((5501970357/156250000000 : ℚ) : ℝ) ≤ stT280 189 := by
  have hc : ((242047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5501970357/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((242047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c190 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((458131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103037/1000000) (δ := 14121/1000000000) (ψ := -188847/125000) 280 234
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t190 : ((41543113557/625000000000 : ℚ) : ℝ) ≤ stT280 190 := by
  have hc : ((229053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41543113557/625000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((229053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c191 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-153093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94099/200000) (δ := 14121/1000000000) (ψ := -188847/125000) 280 234
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t191 : ((-2215847137/100000000000 : ℚ) : ℝ) ≤ stT280 191 := by
  have hc : ((-76559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2215847137/100000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-76559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c192 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-979563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7347683/10000000) (δ := 7007/500000000) (ψ := -188847/125000) 280 235
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t192 : ((-88371868343/1250000000000 : ℚ) : ℝ) ≤ stT280 192 := by
  have hc : ((-979613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88371868343/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-979613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c193 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((1077/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3711323/10000000) (δ := 7007/500000000) (ψ := -188847/125000) 280 235
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t193 : ((1239665393/200000000000 : ℚ) : ℝ) ≤ stT280 193 := by
  have hc : ((8611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1239665393/200000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((8611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c194 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((999297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -93723/10000000) (δ := 7007/500000000) (ψ := -188847/125000) 280 235
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t194 : ((358708688813/5000000000000 : ℚ) : ℝ) ≤ stT280 194 := by
  have hc : ((999247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358708688813/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((999247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c195 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((33579/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3505257/10000000) (δ := 7007/500000000) (ψ := -188847/125000) 280 235
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t195 : ((12019615433/1000000000000 : ℚ) : ℝ) ≤ stT280 195 := by
  have hc : ((33569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12019615433/1000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((33569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c196 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-190633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7085827/10000000) (δ := 7007/500000000) (ψ := -188847/125000) 280 235
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t196 : ((-68086812949/1000000000000 : ℚ) : ℝ) ≤ stT280 196 := by
  have hc : ((-190643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68086812949/1000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-190643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c197 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-109441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2529883/5000000) (δ := 881/62500000) (ψ := -188847/125000) 280 236
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t197 : ((-155964889197/5000000000000 : ℚ) : ℝ) ≤ stT280 197 := by
  have hc : ((-218907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155964889197/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-218907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c198 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((821829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23679/156250) (δ := 881/62500000) (ψ := -188847/125000) 280 236
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t198 : ((584012860151/10000000000000 : ℚ) : ℝ) ≤ stT280 198 := by
  have hc : ((821779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584012860151/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((821779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c199 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((346771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502751/2500000) (δ := 881/62500000) (ψ := -188847/125000) 280 236
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t199 : ((122900825613/2500000000000 : ℚ) : ℝ) ≤ stT280 199 := by
  have hc : ((173373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122900825613/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((173373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c200 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-594871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2759877/5000000) (δ := 881/62500000) (ψ := -188847/125000) 280 236
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t200 : ((-420672803547/10000000000000 : ℚ) : ℝ) ≤ stT280 200 := by
  have hc : ((-594921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-420672803547/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-594921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c201 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-89479/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669689/1000000) (δ := 71/5000000) (ψ := -188847/125000) 280 237
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t201 : ((-7889647683/125000000000 : ℚ) : ℝ) ≤ stT280 201 := by
  have hc : ((-22371/25000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7889647683/125000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-22371/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c202 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((277889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3223/10000) (δ := 71/5000000) (ψ := -188847/125000) 280 237
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t202 : ((195486686883/10000000000000 : ℚ) : ℝ) ≤ stT280 202 := by
  have hc : ((277839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195486686883/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((277839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c203 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((99563/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23381/1000000) (δ := 71/5000000) (ψ := -188847/125000) 280 237
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t203 : ((17468994249/250000000000 : ℚ) : ℝ) ≤ stT280 203 := by
  have hc : ((49779/50000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17468994249/250000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((49779/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c204 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((101179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 367361/1000000) (δ := 71/5000000) (ψ := -188847/125000) 280 237
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t204 : ((3540222903/500000000000 : ℚ) : ℝ) ≤ stT280 204 := by
  have hc : ((101129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3540222903/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((101129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c205 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-954461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709661/1000000) (δ := 71/5000000) (ψ := -188847/125000) 280 237
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t205 : ((-666660072241/10000000000000 : ℚ) : ℝ) ≤ stT280 205 := by
  have hc : ((-954511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-666660072241/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-954511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c206 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-30577/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5205013/10000000) (δ := 14093/1000000000) (ψ := -188847/125000) 280 238
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t206 : ((-85224851247/2500000000000 : ℚ) : ℝ) ≤ stT280 206 := by
  have hc : ((-244641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85224851247/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-244641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c207 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((149557/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1815193/10000000) (δ := 14093/1000000000) (ψ := -188847/125000) 280 238
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t207 : ((12992792907/250000000000 : ℚ) : ℝ) ≤ stT280 207 := by
  have hc : ((149547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12992792907/250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((149547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c208 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((811941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1558317/10000000) (δ := 14093/1000000000) (ψ := -188847/125000) 280 238
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t208 : ((4503559377/80000000000 : ℚ) : ℝ) ≤ stT280 208 := by
  have hc : ((811891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4503559377/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((811891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c209 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-385239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4915657/10000000) (δ := 14093/1000000000) (ψ := -188847/125000) 280 238
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t209 : ((-53302036127/2000000000000 : ℚ) : ℝ) ≤ stT280 209 := by
  have hc : ((-385289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53302036127/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-385289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c210 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-246759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1862749/2500000) (δ := 14017/1000000000) (ψ := -188847/125000) 280 239
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t210 : ((-170288621919/2500000000000 : ℚ) : ℝ) ≤ stT280 210 := by
  have hc : ((-493543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170288621919/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-493543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c211 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-79351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -515697/1250000) (δ := 14017/1000000000) (ψ := -188847/125000) 280 239
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t211 : ((-54661951029/10000000000000 : ℚ) : ℝ) ≤ stT280 211 := by
  have hc : ((-79401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54661951029/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-79401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c212 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((189443/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -407953/5000000) (δ := 14017/1000000000) (ψ := -188847/125000) 280 239
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t212 : ((65051481633/1000000000000 : ℚ) : ℝ) ≤ stT280 212 := by
  have hc : ((189433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65051481633/1000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((189433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c213 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((547611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154889/625000) (δ := 14017/1000000000) (ψ := -188847/125000) 280 239
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t213 : ((93795556617/2500000000000 : ℚ) : ℝ) ≤ stT280 213 := by
  have hc : ((547561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93795556617/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((547561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c214 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-167087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2878477/5000000) (δ := 14017/1000000000) (ψ := -188847/125000) 280 239
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t214 : ((-114226878807/2500000000000 : ℚ) : ℝ) ≤ stT280 214 := by
  have hc : ((-334199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114226878807/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-334199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c215 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-446563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6687609/10000000) (δ := 113/8000000) (ψ := -188847/125000) 280 240
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t215 : ((-15228539153/250000000000 : ℚ) : ℝ) ≤ stT280 215 := by
  have hc : ((-111647/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15228539153/250000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-111647/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c216 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((19383/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3439329/10000000) (δ := 113/8000000) (ψ := -188847/125000) 280 240
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t216 : ((6592521557/500000000000 : ℚ) : ℝ) ≤ stT280 216 := by
  have hc : ((9689/50000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6592521557/500000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((9689/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c217 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((249151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206099/10000000) (δ := 113/8000000) (ψ := -188847/125000) 280 240
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t217 : ((84563087947/1250000000000 : ℚ) : ℝ) ≤ stT280 217 := by
  have hc : ((498277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84563087947/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((498277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c218 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((357771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3012291/10000000) (δ := 113/8000000) (ψ := -188847/125000) 280 240
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t218 : ((48455813497/2000000000000 : ℚ) : ℝ) ≤ stT280 218 := by
  have hc : ((357721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48455813497/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((357721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c219 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-396463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6215981/10000000) (δ := 113/8000000) (ψ := -188847/125000) 280 240
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t219 : ((-16745125509/312500000000 : ℚ) : ℝ) ≤ stT280 219 := by
  have hc : ((-49561/62500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16745125509/312500000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-49561/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c220 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-12713/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6302923/10000000) (δ := 14171/1000000000) (ψ := -188847/125000) 280 241
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t220 : ((-1371461011/25000000000 : ℚ) : ℝ) ≤ stT280 220 := by
  have hc : ((-406841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1371461011/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-406841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c221 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((78519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3128283/10000000) (δ := 14171/1000000000) (ψ := -188847/125000) 280 241
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t221 : ((3300570273/156250000000 : ℚ) : ℝ) ≤ stT280 221 := by
  have hc : ((157013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3300570273/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((157013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c222 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((499959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31937/10000000) (δ := 14171/1000000000) (ψ := -188847/125000) 280 241
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t222 : ((41941712963/625000000000 : ℚ) : ℝ) ≤ stT280 222 := by
  have hc : ((249967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41941712963/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((249967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c223 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((36891/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3178017/10000000) (δ := 14171/1000000000) (ψ := -188847/125000) 280 241
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t223 : ((98799343811/5000000000000 : ℚ) : ℝ) ≤ stT280 223 := by
  have hc : ((147539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98799343811/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((147539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c224 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-815281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6310027/10000000) (δ := 14171/1000000000) (ψ := -188847/125000) 280 241
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t224 : ((-272383334487/5000000000000 : ℚ) : ℝ) ≤ stT280 224 := by
  have hc : ((-815331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272383334487/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-815331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c225 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-404117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -392491/625000) (δ := 879/62500000) (ψ := -188847/125000) 280 242
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t225 : ((-134714067357/2500000000000 : ℚ) : ℝ) ≤ stT280 225 := by
  have hc : ((-202071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134714067357/2500000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-202071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c226 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((11841/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3175671/10000000) (δ := 877/31250000) (ψ := -188847/125000) 280 242
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t226 : ((787518441/40000000000 : ℚ) : ℝ) ≤ stT280 226 := by
  have hc : ((11839/40000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((787518441/40000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((11839/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c227 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((49971/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5321/625000) (δ := 879/62500000) (ψ := -188847/125000) 280 242
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t227 : ((66330485451/1000000000000 : ℚ) : ℝ) ≤ stT280 227 := by
  have hc : ((99937/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66330485451/1000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((99937/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c228 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((365419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373973/1250000) (δ := 879/62500000) (ψ := -188847/125000) 280 242
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t228 : ((120985733077/5000000000000 : ℚ) : ℝ) ≤ stT280 228 := by
  have hc : ((365369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120985733077/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((365369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c229 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-47009/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189227/312500) (δ := 879/62500000) (ψ := -188847/125000) 280 242
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t229 : ((-248532043443/5000000000000 : ℚ) : ℝ) ≤ stT280 229 := by
  have hc : ((-376097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248532043443/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-376097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c230 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-175463/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6602589/10000000) (δ := 7023/500000000) (ψ := -188847/125000) 280 243
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t230 : ((-115703562213/2000000000000 : ℚ) : ℝ) ≤ stT280 230 := by
  have hc : ((-175473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115703562213/2000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-175473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c231 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((14401/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3565709/10000000) (δ := 7023/500000000) (ψ := -188847/125000) 280 243
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t231 : ((2367965649/250000000000 : ℚ) : ℝ) ≤ stT280 231 := by
  have hc : ((3599/25000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2367965649/250000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((3599/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c232 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((61037/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541989/10000000) (δ := 7023/500000000) (ψ := -188847/125000) 280 243
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t232 : ((80141384043/1250000000000 : ℚ) : ℝ) ≤ stT280 232 := by
  have hc : ((488271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80141384043/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((488271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c233 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((34423/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2468781/10000000) (δ := 7023/500000000) (ψ := -188847/125000) 280 243
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t233 : ((180393463439/5000000000000 : ℚ) : ℝ) ≤ stT280 233 := by
  have hc : ((275359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180393463439/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((275359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c234 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-577671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5466671/10000000) (δ := 7023/500000000) (ψ := -188847/125000) 280 243
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t234 : ((-377668349841/10000000000000 : ℚ) : ℝ) ≤ stT280 234 := by
  have hc : ((-577721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377668349841/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-577721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c235 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-19431/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1814053/2500000) (δ := 14153/1000000000) (ψ := -188847/125000) 280 244
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t235 : ((-1584507141/25000000000 : ℚ) : ℝ) ≤ stT280 235 := by
  have hc : ((-2429/2500 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1584507141/25000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-2429/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c236 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-889/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2141901/5000000) (δ := 14153/1000000000) (ψ := -188847/125000) 280 244
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t236 : ((-1852459281/200000000000 : ℚ) : ℝ) ≤ stT280 236 := by
  have hc : ((-14229/100000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1852459281/200000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-14229/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c237 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((863011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165499/1250000) (δ := 14153/1000000000) (ψ := -188847/125000) 280 244
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t237 : ((560552713809/10000000000000 : ℚ) : ℝ) ≤ stT280 237 := by
  have hc : ((862961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((560552713809/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((862961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c238 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((796481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811679/5000000) (δ := 14153/1000000000) (ψ := -188847/125000) 280 244
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t238 : ((516248963493/10000000000000 : ℚ) : ℝ) ≤ stT280 238 := by
  have hc : ((796431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516248963493/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((796431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c239 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-124941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1139597/2500000) (δ := 14153/1000000000) (ψ := -188847/125000) 280 244
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t239 : ((-40416941101/2500000000000 : ℚ) : ℝ) ≤ stT280 239 := by
  have hc : ((-62483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40416941101/2500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-62483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c240 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-988901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467573/625000) (δ := 14153/1000000000) (ψ := -188847/125000) 280 244
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t240 : ((-319182946299/5000000000000 : ℚ) : ℝ) ≤ stT280 240 := by
  have hc : ((-988951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319182946299/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-988951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c241 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-527523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1329049/2500000) (δ := 14143/1000000000) (ψ := -188847/125000) 280 245
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t241 : ((-339839840961/10000000000000 : ℚ) : ℝ) ≤ stT280 241 := by
  have hc : ((-527573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339839840961/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-527573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c242 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((567727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604409/2500000) (δ := 14143/1000000000) (ψ := -188847/125000) 280 245
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t242 : ((45614549981/1250000000000 : ℚ) : ℝ) ≤ stT280 242 := by
  have hc : ((567677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45614549981/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((567677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c243 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((491229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 234477/5000000) (δ := 14143/1000000000) (ψ := -188847/125000) 280 245
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t243 : ((157553683/2500000000 : ℚ) : ℝ) ≤ stT280 243 := by
  have hc : ((122801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157553683/2500000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((122801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c244 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((289/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1671857/5000000) (δ := 14143/1000000000) (ψ := -188847/125000) 280 245
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t244 : ((369946329/25000000000 : ℚ) : ℝ) ≤ stT280 244 := by
  have hc : ((4623/20000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369946329/25000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((4623/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c245 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-790653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6206679/10000000) (δ := 28143/1000000000) (ψ := -188847/125000) 280 245
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t245 : ((-505161960531/10000000000000 : ℚ) : ℝ) ≤ stT280 245 := by
  have hc : ((-790703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505161960531/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-790703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c246 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-886247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6649939/10000000) (δ := 2807/200000000) (ψ := -188847/125000) 280 246
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t246 : ((-565082582369/10000000000000 : ℚ) : ℝ) ≤ stT280 246 := by
  have hc : ((-886297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-565082582369/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-886297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c247 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((11677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3810179/10000000) (δ := 2807/200000000) (ψ := -188847/125000) 280 246
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t247 : ((3710967359/1250000000000 : ℚ) : ℝ) ≤ stT280 247 := by
  have hc : ((23329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3710967359/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((23329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c248 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((57741/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -981899/10000000) (δ := 2807/200000000) (ψ := -188847/125000) 280 246
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t248 : ((58661681/1000000000 : ℚ) : ℝ) ≤ stT280 248 := by
  have hc : ((461903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58661681/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((461903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c249 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((742509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1834971/10000000) (δ := 2807/200000000) (ψ := -188847/125000) 280 246
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t249 : ((117628521829/2500000000000 : ℚ) : ℝ) ≤ stT280 249 := by
  have hc : ((742459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117628521829/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((742459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_c250 :
    |Real.cos (((280 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((-281599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4640641/10000000) (δ := 2807/200000000) (ψ := -188847/125000) 280 246
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st280_t250 : ((-22266324993/1250000000000 : ℚ) : ℝ) ≤ stT280 250 := by
  have hc : ((-281649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((280 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st280_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22266324993/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-281649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st280_p1 : ((29967/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT280 (i+1) := by
  rw [Finset.sum_range_one]
  exact st280_t1

theorem st280_p2 : ((5457891348901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT280 (i+1))
      = (∑ i ∈ Finset.range 1, stT280 (i+1)) + stT280 2 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 1
    simpa using h
  have hprev := st280_p1
  have hstep := st280_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p3 : ((7299326717793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT280 (i+1))
      = (∑ i ∈ Finset.range 2, stT280 (i+1)) + stT280 3 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 2
    simpa using h
  have hprev := st280_p2
  have hstep := st280_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p4 : ((12265646717793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT280 (i+1))
      = (∑ i ∈ Finset.range 3, stT280 (i+1)) + stT280 4 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 3
    simpa using h
  have hprev := st280_p3
  have hstep := st280_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p5 : ((4153414402717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT280 (i+1))
      = (∑ i ∈ Finset.range 4, stT280 (i+1)) + stT280 5 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 4
    simpa using h
  have hprev := st280_p4
  have hstep := st280_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p6 : ((10048429915321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT280 (i+1))
      = (∑ i ∈ Finset.range 5, stT280 (i+1)) + stT280 6 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 5
    simpa using h
  have hprev := st280_p5
  have hstep := st280_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p7 : ((11868931354539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT280 (i+1))
      = (∑ i ∈ Finset.range 6, stT280 (i+1)) + stT280 7 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 6
    simpa using h
  have hprev := st280_p6
  have hstep := st280_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p8 : ((13345744701837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT280 (i+1))
      = (∑ i ∈ Finset.range 7, stT280 (i+1)) + stT280 8 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 7
    simpa using h
  have hprev := st280_p7
  have hstep := st280_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p9 : ((3567991985637/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT280 (i+1))
      = (∑ i ∈ Finset.range 8, stT280 (i+1)) + stT280 9 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 8
    simpa using h
  have hprev := st280_p8
  have hstep := st280_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p10 : ((1217016718709/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT280 (i+1))
      = (∑ i ∈ Finset.range 9, stT280 (i+1)) + stT280 10 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 9
    simpa using h
  have hprev := st280_p9
  have hstep := st280_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p11 : ((16439059462361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT280 (i+1))
      = (∑ i ∈ Finset.range 10, stT280 (i+1)) + stT280 11 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 10
    simpa using h
  have hprev := st280_p10
  have hstep := st280_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p12 : ((17866384626801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT280 (i+1))
      = (∑ i ∈ Finset.range 11, stT280 (i+1)) + stT280 12 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 11
    simpa using h
  have hprev := st280_p11
  have hstep := st280_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p13 : ((33061003043783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT280 (i+1))
      = (∑ i ∈ Finset.range 12, stT280 (i+1)) + stT280 13 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 12
    simpa using h
  have hprev := st280_p12
  have hstep := st280_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p14 : ((34573827048547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT280 (i+1))
      = (∑ i ∈ Finset.range 13, stT280 (i+1)) + stT280 14 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 13
    simpa using h
  have hprev := st280_p13
  have hstep := st280_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p15 : ((1473555660539/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT280 (i+1))
      = (∑ i ∈ Finset.range 14, stT280 (i+1)) + stT280 15 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 14
    simpa using h
  have hprev := st280_p14
  have hstep := st280_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p16 : ((1502284260539/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT280 (i+1))
      = (∑ i ∈ Finset.range 15, stT280 (i+1)) + stT280 16 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 15
    simpa using h
  have hprev := st280_p15
  have hstep := st280_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p17 : ((17565907499057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT280 (i+1))
      = (∑ i ∈ Finset.range 16, stT280 (i+1)) + stT280 17 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 16
    simpa using h
  have hprev := st280_p16
  have hstep := st280_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p18 : ((1869716374349/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT280 (i+1))
      = (∑ i ∈ Finset.range 17, stT280 (i+1)) + stT280 18 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 17
    simpa using h
  have hprev := st280_p17
  have hstep := st280_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p19 : ((17596359057429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT280 (i+1))
      = (∑ i ∈ Finset.range 18, stT280 (i+1)) + stT280 19 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 18
    simpa using h
  have hprev := st280_p18
  have hstep := st280_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p20 : ((17529006453201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT280 (i+1))
      = (∑ i ∈ Finset.range 19, stT280 (i+1)) + stT280 20 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 19
    simpa using h
  have hprev := st280_p19
  have hstep := st280_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p21 : ((9233473463947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT280 (i+1))
      = (∑ i ∈ Finset.range 20, stT280 (i+1)) + stT280 21 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 20
    simpa using h
  have hprev := st280_p20
  have hstep := st280_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p22 : ((19529746021373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT280 (i+1))
      = (∑ i ∈ Finset.range 21, stT280 (i+1)) + stT280 22 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 21
    simpa using h
  have hprev := st280_p21
  have hstep := st280_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p23 : ((20552146338317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT280 (i+1))
      = (∑ i ∈ Finset.range 22, stT280 (i+1)) + stT280 23 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 22
    simpa using h
  have hprev := st280_p22
  have hstep := st280_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p24 : ((42456796509583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT280 (i+1))
      = (∑ i ∈ Finset.range 23, stT280 (i+1)) + stT280 24 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 23
    simpa using h
  have hprev := st280_p23
  have hstep := st280_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p25 : ((20828021054603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT280 (i+1))
      = (∑ i ∈ Finset.range 24, stT280 (i+1)) + stT280 25 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 24
    simpa using h
  have hprev := st280_p24
  have hstep := st280_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p26 : ((19934888268183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT280 (i+1))
      = (∑ i ∈ Finset.range 25, stT280 (i+1)) + stT280 26 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 25
    simpa using h
  have hprev := st280_p25
  have hstep := st280_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p27 : ((20660257336683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT280 (i+1))
      = (∑ i ∈ Finset.range 26, stT280 (i+1)) + stT280 27 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 26
    simpa using h
  have hprev := st280_p26
  have hstep := st280_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p28 : ((20569859543301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT280 (i+1))
      = (∑ i ∈ Finset.range 27, stT280 (i+1)) + stT280 28 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 27
    simpa using h
  have hprev := st280_p27
  have hstep := st280_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p29 : ((20290978477673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT280 (i+1))
      = (∑ i ∈ Finset.range 28, stT280 (i+1)) + stT280 29 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 28
    simpa using h
  have hprev := st280_p28
  have hstep := st280_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p30 : ((41246612489173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT280 (i+1))
      = (∑ i ∈ Finset.range 29, stT280 (i+1)) + stT280 30 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 29
    simpa using h
  have hprev := st280_p29
  have hstep := st280_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p31 : ((41015370536673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT280 (i+1))
      = (∑ i ∈ Finset.range 30, stT280 (i+1)) + stT280 31 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 30
    simpa using h
  have hprev := st280_p30
  have hstep := st280_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p32 : ((20158493833409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT280 (i+1))
      = (∑ i ∈ Finset.range 31, stT280 (i+1)) + stT280 32 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 31
    simpa using h
  have hprev := st280_p31
  have hstep := st280_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p33 : ((20974269338349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT280 (i+1))
      = (∑ i ∈ Finset.range 32, stT280 (i+1)) + stT280 33 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 32
    simpa using h
  have hprev := st280_p32
  have hstep := st280_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p34 : ((1270244468121/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT280 (i+1))
      = (∑ i ∈ Finset.range 33, stT280 (i+1)) + stT280 34 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 33
    simpa using h
  have hprev := st280_p33
  have hstep := st280_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p35 : ((39916414443409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT280 (i+1))
      = (∑ i ∈ Finset.range 34, stT280 (i+1)) + stT280 35 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 34
    simpa using h
  have hprev := st280_p34
  have hstep := st280_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p36 : ((41442485499647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT280 (i+1))
      = (∑ i ∈ Finset.range 35, stT280 (i+1)) + stT280 36 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 35
    simpa using h
  have hprev := st280_p35
  have hstep := st280_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p37 : ((10591250426763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT280 (i+1))
      = (∑ i ∈ Finset.range 36, stT280 (i+1)) + stT280 37 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 36
    simpa using h
  have hprev := st280_p36
  have hstep := st280_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p38 : ((10366242717403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT280 (i+1))
      = (∑ i ∈ Finset.range 37, stT280 (i+1)) + stT280 38 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 37
    simpa using h
  have hprev := st280_p37
  have hstep := st280_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p39 : ((9965912609711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT280 (i+1))
      = (∑ i ∈ Finset.range 38, stT280 (i+1)) + stT280 39 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 38
    simpa using h
  have hprev := st280_p38
  have hstep := st280_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p40 : ((9694216008507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT280 (i+1))
      = (∑ i ∈ Finset.range 39, stT280 (i+1)) + stT280 40 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 39
    simpa using h
  have hprev := st280_p39
  have hstep := st280_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p41 : ((19289477954727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT280 (i+1))
      = (∑ i ∈ Finset.range 40, stT280 (i+1)) + stT280 41 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 40
    simpa using h
  have hprev := st280_p40
  have hstep := st280_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p42 : ((19544640063739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT280 (i+1))
      = (∑ i ∈ Finset.range 41, stT280 (i+1)) + stT280 42 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 41
    simpa using h
  have hprev := st280_p41
  have hstep := st280_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p43 : ((40002952015453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT280 (i+1))
      = (∑ i ∈ Finset.range 42, stT280 (i+1)) + stT280 43 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 42
    simpa using h
  have hprev := st280_p42
  have hstep := st280_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p44 : ((41080498772237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT280 (i+1))
      = (∑ i ∈ Finset.range 43, stT280 (i+1)) + stT280 44 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 43
    simpa using h
  have hprev := st280_p43
  have hstep := st280_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p45 : ((42155548861263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT280 (i+1))
      = (∑ i ∈ Finset.range 44, stT280 (i+1)) + stT280 45 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 44
    simpa using h
  have hprev := st280_p44
  have hstep := st280_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p46 : ((21539259468327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT280 (i+1))
      = (∑ i ∈ Finset.range 45, stT280 (i+1)) + stT280 46 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 45
    simpa using h
  have hprev := st280_p45
  have hstep := st280_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p47 : ((5458326765397/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT280 (i+1))
      = (∑ i ∈ Finset.range 46, stT280 (i+1)) + stT280 47 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 46
    simpa using h
  have hprev := st280_p46
  have hstep := st280_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p48 : ((43705231621301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT280 (i+1))
      = (∑ i ∈ Finset.range 47, stT280 (i+1)) + stT280 48 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 47
    simpa using h
  have hprev := st280_p47
  have hstep := st280_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p49 : ((43041675641593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT280 (i+1))
      = (∑ i ∈ Finset.range 48, stT280 (i+1)) + stT280 49 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 48
    simpa using h
  have hprev := st280_p48
  have hstep := st280_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p50 : ((41775271046231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT280 (i+1))
      = (∑ i ∈ Finset.range 49, stT280 (i+1)) + stT280 50 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 49
    simpa using h
  have hprev := st280_p49
  have hstep := st280_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p51 : ((20214161274339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT280 (i+1))
      = (∑ i ∈ Finset.range 50, stT280 (i+1)) + stT280 51 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 50
    simpa using h
  have hprev := st280_p50
  have hstep := st280_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p52 : ((39828043803561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT280 (i+1))
      = (∑ i ∈ Finset.range 51, stT280 (i+1)) + stT280 52 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 51
    simpa using h
  have hprev := st280_p51
  have hstep := st280_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p53 : ((40489014287931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT280 (i+1))
      = (∑ i ∈ Finset.range 52, stT280 (i+1)) + stT280 53 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 52
    simpa using h
  have hprev := st280_p52
  have hstep := st280_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p54 : ((10462379692983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT280 (i+1))
      = (∑ i ∈ Finset.range 53, stT280 (i+1)) + stT280 54 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 53
    simpa using h
  have hprev := st280_p53
  have hstep := st280_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p55 : ((42429496195009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT280 (i+1))
      = (∑ i ∈ Finset.range 54, stT280 (i+1)) + stT280 55 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 54
    simpa using h
  have hprev := st280_p54
  have hstep := st280_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p56 : ((165908243011/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT280 (i+1))
      = (∑ i ∈ Finset.range 55, stT280 (i+1)) + stT280 56 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 55
    simpa using h
  have hprev := st280_p55
  have hstep := st280_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p57 : ((20173836924353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT280 (i+1))
      = (∑ i ∈ Finset.range 56, stT280 (i+1)) + stT280 57 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 56
    simpa using h
  have hprev := st280_p56
  have hstep := st280_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p58 : ((4084986305389/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT280 (i+1))
      = (∑ i ∈ Finset.range 57, stT280 (i+1)) + stT280 58 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 57
    simpa using h
  have hprev := st280_p57
  have hstep := st280_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p59 : ((42086224074853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT280 (i+1))
      = (∑ i ∈ Finset.range 58, stT280 (i+1)) + stT280 59 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 58
    simpa using h
  have hprev := st280_p58
  have hstep := st280_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p60 : ((5209262306251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT280 (i+1))
      = (∑ i ∈ Finset.range 59, stT280 (i+1)) + stT280 60 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 59
    simpa using h
  have hprev := st280_p59
  have hstep := st280_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p61 : ((40499297154427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT280 (i+1))
      = (∑ i ∈ Finset.range 60, stT280 (i+1)) + stT280 61 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 60
    simpa using h
  have hprev := st280_p60
  have hstep := st280_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p62 : ((8236592310549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT280 (i+1))
      = (∑ i ∈ Finset.range 61, stT280 (i+1)) + stT280 62 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 61
    simpa using h
  have hprev := st280_p61
  have hstep := st280_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p63 : ((8411992943369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT280 (i+1))
      = (∑ i ∈ Finset.range 62, stT280 (i+1)) + stT280 63 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 62
    simpa using h
  have hprev := st280_p62
  have hstep := st280_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p64 : ((20471917536971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT280 (i+1))
      = (∑ i ∈ Finset.range 63, stT280 (i+1)) + stT280 64 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 63
    simpa using h
  have hprev := st280_p63
  have hstep := st280_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p65 : ((20412476959941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT280 (i+1))
      = (∑ i ∈ Finset.range 64, stT280 (i+1)) + stT280 65 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 64
    simpa using h
  have hprev := st280_p64
  have hstep := st280_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p66 : ((20992353159857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT280 (i+1))
      = (∑ i ∈ Finset.range 65, stT280 (i+1)) + stT280 66 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 65
    simpa using h
  have hprev := st280_p65
  have hstep := st280_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p67 : ((41072213772349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT280 (i+1))
      = (∑ i ∈ Finset.range 66, stT280 (i+1)) + stT280 67 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 66
    simpa using h
  have hprev := st280_p66
  have hstep := st280_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p68 : ((20437493648913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT280 (i+1))
      = (∑ i ∈ Finset.range 67, stT280 (i+1)) + stT280 68 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 67
    simpa using h
  have hprev := st280_p67
  have hstep := st280_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p69 : ((20976445225359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT280 (i+1))
      = (∑ i ∈ Finset.range 68, stT280 (i+1)) + stT280 69 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 68
    simpa using h
  have hprev := st280_p68
  have hstep := st280_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p70 : ((10216085104971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT280 (i+1))
      = (∑ i ∈ Finset.range 69, stT280 (i+1)) + stT280 70 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 69
    simpa using h
  have hprev := st280_p69
  have hstep := st280_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p71 : ((5153977504481/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT280 (i+1))
      = (∑ i ∈ Finset.range 70, stT280 (i+1)) + stT280 71 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 70
    simpa using h
  have hprev := st280_p70
  have hstep := st280_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p72 : ((20877321435389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT280 (i+1))
      = (∑ i ∈ Finset.range 71, stT280 (i+1)) + stT280 72 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 71
    simpa using h
  have hprev := st280_p71
  have hstep := st280_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p73 : ((32537849117/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT280 (i+1))
      = (∑ i ∈ Finset.range 72, stT280 (i+1)) + stT280 73 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 72
    simpa using h
  have hprev := st280_p72
  have hstep := st280_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p74 : ((20895142745009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT280 (i+1))
      = (∑ i ∈ Finset.range 73, stT280 (i+1)) + stT280 74 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 73
    simpa using h
  have hprev := st280_p73
  have hstep := st280_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p75 : ((10266824292923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT280 (i+1))
      = (∑ i ∈ Finset.range 74, stT280 (i+1)) + stT280 75 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 74
    simpa using h
  have hprev := st280_p74
  have hstep := st280_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p76 : ((5149066606697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT280 (i+1))
      = (∑ i ∈ Finset.range 75, stT280 (i+1)) + stT280 76 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 75
    simpa using h
  have hprev := st280_p75
  have hstep := st280_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p77 : ((20822921325633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT280 (i+1))
      = (∑ i ∈ Finset.range 76, stT280 (i+1)) + stT280 77 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 76
    simpa using h
  have hprev := st280_p76
  have hstep := st280_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p78 : ((4077272949813/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT280 (i+1))
      = (∑ i ∈ Finset.range 77, stT280 (i+1)) + stT280 78 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 77
    simpa using h
  have hprev := st280_p77
  have hstep := st280_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p79 : ((41858498082741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT280 (i+1))
      = (∑ i ∈ Finset.range 78, stT280 (i+1)) + stT280 79 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 78
    simpa using h
  have hprev := st280_p78
  have hstep := st280_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p80 : ((40747858759617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT280 (i+1))
      = (∑ i ∈ Finset.range 79, stT280 (i+1)) + stT280 80 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 79
    simpa using h
  have hprev := st280_p79
  have hstep := st280_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p81 : ((41747225326347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT280 (i+1))
      = (∑ i ∈ Finset.range 80, stT280 (i+1)) + stT280 81 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 80
    simpa using h
  have hprev := st280_p80
  have hstep := st280_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p82 : ((40936339339339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT280 (i+1))
      = (∑ i ∈ Finset.range 81, stT280 (i+1)) + stT280 82 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 81
    simpa using h
  have hprev := st280_p81
  have hstep := st280_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p83 : ((41530587351151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT280 (i+1))
      = (∑ i ∈ Finset.range 82, stT280 (i+1)) + stT280 83 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 82
    simpa using h
  have hprev := st280_p82
  have hstep := st280_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p84 : ((41145746815071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT280 (i+1))
      = (∑ i ∈ Finset.range 83, stT280 (i+1)) + stT280 84 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 83
    simpa using h
  have hprev := st280_p83
  have hstep := st280_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p85 : ((41348792584819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT280 (i+1))
      = (∑ i ∈ Finset.range 84, stT280 (i+1)) + stT280 85 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 84
    simpa using h
  have hprev := st280_p84
  have hstep := st280_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p86 : ((41289381025331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT280 (i+1))
      = (∑ i ∈ Finset.range 85, stT280 (i+1)) + stT280 86 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 85
    simpa using h
  have hprev := st280_p85
  have hstep := st280_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p87 : ((20623020428653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT280 (i+1))
      = (∑ i ∈ Finset.range 86, stT280 (i+1)) + stT280 87 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 86
    simpa using h
  have hprev := st280_p86
  have hstep := st280_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p88 : ((1033779198529/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT280 (i+1))
      = (∑ i ∈ Finset.range 87, stT280 (i+1)) + stT280 88 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 87
    simpa using h
  have hprev := st280_p87
  have hstep := st280_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p89 : ((2061153359143/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT280 (i+1))
      = (∑ i ∈ Finset.range 88, stT280 (i+1)) + stT280 89 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 88
    simpa using h
  have hprev := st280_p88
  have hstep := st280_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p90 : ((10334166142379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT280 (i+1))
      = (∑ i ∈ Finset.range 89, stT280 (i+1)) + stT280 90 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 89
    simpa using h
  have hprev := st280_p89
  have hstep := st280_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p91 : ((20636670932903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT280 (i+1))
      = (∑ i ∈ Finset.range 90, stT280 (i+1)) + stT280 91 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 90
    simpa using h
  have hprev := st280_p90
  have hstep := st280_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p92 : ((10312832244871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT280 (i+1))
      = (∑ i ∈ Finset.range 91, stT280 (i+1)) + stT280 92 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 91
    simpa using h
  have hprev := st280_p91
  have hstep := st280_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p93 : ((1655658542983/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT280 (i+1))
      = (∑ i ∈ Finset.range 92, stT280 (i+1)) + stT280 93 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 92
    simpa using h
  have hprev := st280_p92
  have hstep := st280_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p94 : ((41103880429691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT280 (i+1))
      = (∑ i ∈ Finset.range 93, stT280 (i+1)) + stT280 94 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 93
    simpa using h
  have hprev := st280_p93
  have hstep := st280_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p95 : ((41560339067869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT280 (i+1))
      = (∑ i ∈ Finset.range 94, stT280 (i+1)) + stT280 95 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 94
    simpa using h
  have hprev := st280_p94
  have hstep := st280_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p96 : ((40925898600607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT280 (i+1))
      = (∑ i ∈ Finset.range 95, stT280 (i+1)) + stT280 96 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 95
    simpa using h
  have hprev := st280_p95
  have hstep := st280_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p97 : ((8345587736447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT280 (i+1))
      = (∑ i ∈ Finset.range 96, stT280 (i+1)) + stT280 97 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 96
    simpa using h
  have hprev := st280_p96
  have hstep := st280_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p98 : ((40793690598961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT280 (i+1))
      = (∑ i ∈ Finset.range 97, stT280 (i+1)) + stT280 98 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 97
    simpa using h
  have hprev := st280_p97
  have hstep := st280_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p99 : ((20897243673929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT280 (i+1))
      = (∑ i ∈ Finset.range 98, stT280 (i+1)) + stT280 99 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 98
    simpa using h
  have hprev := st280_p98
  have hstep := st280_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p100 : ((20411097173929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT280 (i+1))
      = (∑ i ∈ Finset.range 99, stT280 (i+1)) + stT280 100 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 99
    simpa using h
  have hprev := st280_p99
  have hstep := st280_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p101 : ((41648050181933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT280 (i+1))
      = (∑ i ∈ Finset.range 100, stT280 (i+1)) + stT280 101 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 100
    simpa using h
  have hprev := st280_p100
  have hstep := st280_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p102 : ((8218405326329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT280 (i+1))
      = (∑ i ∈ Finset.range 101, stT280 (i+1)) + stT280 102 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 101
    simpa using h
  have hprev := st280_p101
  have hstep := st280_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p103 : ((41274503650471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT280 (i+1))
      = (∑ i ∈ Finset.range 102, stT280 (i+1)) + stT280 103 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 102
    simpa using h
  have hprev := st280_p102
  have hstep := st280_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p104 : ((41516998142731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT280 (i+1))
      = (∑ i ∈ Finset.range 103, stT280 (i+1)) + stT280 104 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 103
    simpa using h
  have hprev := st280_p103
  have hstep := st280_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p105 : ((5109911344347/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT280 (i+1))
      = (∑ i ∈ Finset.range 104, stT280 (i+1)) + stT280 105 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 104
    simpa using h
  have hprev := st280_p104
  have hstep := st280_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p106 : ((41784387538451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT280 (i+1))
      = (∑ i ∈ Finset.range 105, stT280 (i+1)) + stT280 106 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 105
    simpa using h
  have hprev := st280_p105
  have hstep := st280_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p107 : ((40827234769069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT280 (i+1))
      = (∑ i ∈ Finset.range 106, stT280 (i+1)) + stT280 107 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 106
    simpa using h
  have hprev := st280_p106
  have hstep := st280_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p108 : ((41576491693819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT280 (i+1))
      = (∑ i ∈ Finset.range 107, stT280 (i+1)) + stT280 108 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 107
    simpa using h
  have hprev := st280_p107
  have hstep := st280_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p109 : ((8252914683123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT280 (i+1))
      = (∑ i ∈ Finset.range 108, stT280 (i+1)) + stT280 109 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 108
    simpa using h
  have hprev := st280_p108
  have hstep := st280_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p110 : ((5128251048981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT280 (i+1))
      = (∑ i ∈ Finset.range 109, stT280 (i+1)) + stT280 110 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 109
    simpa using h
  have hprev := st280_p109
  have hstep := st280_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p111 : ((1043639012923/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT280 (i+1))
      = (∑ i ∈ Finset.range 110, stT280 (i+1)) + stT280 111 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 110
    simpa using h
  have hprev := st280_p110
  have hstep := st280_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p112 : ((5100452415031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT280 (i+1))
      = (∑ i ∈ Finset.range 111, stT280 (i+1)) + stT280 112 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 111
    simpa using h
  have hprev := st280_p111
  have hstep := st280_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p113 : ((5199272346461/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT280 (i+1))
      = (∑ i ∈ Finset.range 112, stT280 (i+1)) + stT280 113 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 112
    simpa using h
  have hprev := st280_p112
  have hstep := st280_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p114 : ((20648226065539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT280 (i+1))
      = (∑ i ∈ Finset.range 113, stT280 (i+1)) + stT280 114 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 113
    simpa using h
  have hprev := st280_p113
  have hstep := st280_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p115 : ((20478420635059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT280 (i+1))
      = (∑ i ∈ Finset.range 114, stT280 (i+1)) + stT280 115 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 114
    simpa using h
  have hprev := st280_p114
  have hstep := st280_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p116 : ((20890016831287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT280 (i+1))
      = (∑ i ∈ Finset.range 115, stT280 (i+1)) + stT280 116 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 115
    simpa using h
  have hprev := st280_p115
  have hstep := st280_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p117 : ((10221485799617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT280 (i+1))
      = (∑ i ∈ Finset.range 116, stT280 (i+1)) + stT280 117 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 116
    simpa using h
  have hprev := st280_p116
  have hstep := st280_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p118 : ((20685417189883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT280 (i+1))
      = (∑ i ∈ Finset.range 117, stT280 (i+1)) + stT280 118 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 117
    simpa using h
  have hprev := st280_p117
  have hstep := st280_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p119 : ((831486973387/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT280 (i+1))
      = (∑ i ∈ Finset.range 118, stT280 (i+1)) + stT280 119 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 118
    simpa using h
  have hprev := st280_p118
  have hstep := st280_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p120 : ((20397648627491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT280 (i+1))
      = (∑ i ∈ Finset.range 119, stT280 (i+1)) + stT280 120 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 119
    simpa using h
  have hprev := st280_p119
  have hstep := st280_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p121 : ((10417880231053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT280 (i+1))
      = (∑ i ∈ Finset.range 120, stT280 (i+1)) + stT280 121 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 120
    simpa using h
  have hprev := st280_p120
  have hstep := st280_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p122 : ((515826564389/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT280 (i+1))
      = (∑ i ∈ Finset.range 121, stT280 (i+1)) + stT280 122 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 121
    simpa using h
  have hprev := st280_p121
  have hstep := st280_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p123 : ((4092189910357/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT280 (i+1))
      = (∑ i ∈ Finset.range 122, stT280 (i+1)) + stT280 123 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 122
    simpa using h
  have hprev := st280_p122
  have hstep := st280_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p124 : ((20889247786043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT280 (i+1))
      = (∑ i ∈ Finset.range 123, stT280 (i+1)) + stT280 124 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 123
    simpa using h
  have hprev := st280_p123
  have hstep := st280_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p125 : ((20517072717531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT280 (i+1))
      = (∑ i ∈ Finset.range 124, stT280 (i+1)) + stT280 125 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 124
    simpa using h
  have hprev := st280_p124
  have hstep := st280_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p126 : ((20549312411961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT280 (i+1))
      = (∑ i ∈ Finset.range 125, stT280 (i+1)) + stT280 126 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 125
    simpa using h
  have hprev := st280_p125
  have hstep := st280_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p127 : ((20884272442197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT280 (i+1))
      = (∑ i ∈ Finset.range 126, stT280 (i+1)) + stT280 127 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 126
    simpa using h
  have hprev := st280_p126
  have hstep := st280_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p128 : ((4090796802159/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT280 (i+1))
      = (∑ i ∈ Finset.range 127, stT280 (i+1)) + stT280 128 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 127
    simpa using h
  have hprev := st280_p127
  have hstep := st280_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p129 : ((4123273961309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT280 (i+1))
      = (∑ i ∈ Finset.range 128, stT280 (i+1)) + stT280 129 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 128
    simpa using h
  have hprev := st280_p128
  have hstep := st280_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p130 : ((10432266903087/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT280 (i+1))
      = (∑ i ∈ Finset.range 129, stT280 (i+1)) + stT280 130 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 129
    simpa using h
  have hprev := st280_p129
  have hstep := st280_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p131 : ((2553476982093/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT280 (i+1))
      = (∑ i ∈ Finset.range 130, stT280 (i+1)) + stT280 131 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 130
    simpa using h
  have hprev := st280_p130
  have hstep := st280_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p132 : ((2581055661067/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT280 (i+1))
      = (∑ i ∈ Finset.range 131, stT280 (i+1)) + stT280 132 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 131
    simpa using h
  have hprev := st280_p131
  have hstep := st280_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p133 : ((8342002677541/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT280 (i+1))
      = (∑ i ∈ Finset.range 132, stT280 (i+1)) + stT280 133 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 132
    simpa using h
  have hprev := st280_p132
  have hstep := st280_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p134 : ((40846488207567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT280 (i+1))
      = (∑ i ∈ Finset.range 133, stT280 (i+1)) + stT280 134 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 133
    simpa using h
  have hprev := st280_p133
  have hstep := st280_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p135 : ((41289621554817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT280 (i+1))
      = (∑ i ∈ Finset.range 134, stT280 (i+1)) + stT280 135 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 134
    simpa using h
  have hprev := st280_p134
  have hstep := st280_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p136 : ((41726205889189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT280 (i+1))
      = (∑ i ∈ Finset.range 135, stT280 (i+1)) + stT280 136 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 135
    simpa using h
  have hprev := st280_p135
  have hstep := st280_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p137 : ((40873038009883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT280 (i+1))
      = (∑ i ∈ Finset.range 136, stT280 (i+1)) + stT280 137 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 136
    simpa using h
  have hprev := st280_p136
  have hstep := st280_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p138 : ((41213739603787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT280 (i+1))
      = (∑ i ∈ Finset.range 137, stT280 (i+1)) + stT280 138 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 137
    simpa using h
  have hprev := st280_p137
  have hstep := st280_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p139 : ((41765340009451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT280 (i+1))
      = (∑ i ∈ Finset.range 138, stT280 (i+1)) + stT280 139 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 138
    simpa using h
  have hprev := st280_p138
  have hstep := st280_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p140 : ((20475572786283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT280 (i+1))
      = (∑ i ∈ Finset.range 139, stT280 (i+1)) + stT280 140 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 139
    simpa using h
  have hprev := st280_p139
  have hstep := st280_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p141 : ((41077266948477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT280 (i+1))
      = (∑ i ∈ Finset.range 140, stT280 (i+1)) + stT280 141 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 140
    simpa using h
  have hprev := st280_p140
  have hstep := st280_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p142 : ((5223617323929/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT280 (i+1))
      = (∑ i ∈ Finset.range 141, stT280 (i+1)) + stT280 142 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 141
    simpa using h
  have hprev := st280_p141
  have hstep := st280_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p143 : ((4110745573847/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT280 (i+1))
      = (∑ i ∈ Finset.range 142, stT280 (i+1)) + stT280 143 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 142
    simpa using h
  have hprev := st280_p142
  have hstep := st280_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p144 : ((5113883093503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT280 (i+1))
      = (∑ i ∈ Finset.range 143, stT280 (i+1)) + stT280 144 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 143
    simpa using h
  have hprev := st280_p143
  have hstep := st280_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p145 : ((10433641962011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT280 (i+1))
      = (∑ i ∈ Finset.range 144, stT280 (i+1)) + stT280 145 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 144
    simpa using h
  have hprev := st280_p144
  have hstep := st280_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p146 : ((323049778321/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT280 (i+1))
      = (∑ i ∈ Finset.range 145, stT280 (i+1)) + stT280 146 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 145
    simpa using h
  have hprev := st280_p145
  have hstep := st280_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p147 : ((20394775553071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT280 (i+1))
      = (∑ i ∈ Finset.range 146, stT280 (i+1)) + stT280 147 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 146
    simpa using h
  have hprev := st280_p146
  have hstep := st280_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p148 : ((10385006057549/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT280 (i+1))
      = (∑ i ∈ Finset.range 147, stT280 (i+1)) + stT280 148 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 147
    simpa using h
  have hprev := st280_p147
  have hstep := st280_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p149 : ((41626142612147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT280 (i+1))
      = (∑ i ∈ Finset.range 148, stT280 (i+1)) + stT280 149 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 148
    simpa using h
  have hprev := st280_p148
  have hstep := st280_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p150 : ((4082535419793/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT280 (i+1))
      = (∑ i ∈ Finset.range 149, stT280 (i+1)) + stT280 150 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 149
    simpa using h
  have hprev := st280_p149
  have hstep := st280_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p151 : ((824114618319/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT280 (i+1))
      = (∑ i ∈ Finset.range 150, stT280 (i+1)) + stT280 151 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 150
    simpa using h
  have hprev := st280_p150
  have hstep := st280_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p152 : ((20895735106893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT280 (i+1))
      = (∑ i ∈ Finset.range 151, stT280 (i+1)) + stT280 152 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 151
    simpa using h
  have hprev := st280_p151
  have hstep := st280_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p153 : ((20549359886667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT280 (i+1))
      = (∑ i ∈ Finset.range 152, stT280 (i+1)) + stT280 153 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 152
    simpa using h
  have hprev := st280_p152
  have hstep := st280_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p154 : ((40869504226807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT280 (i+1))
      = (∑ i ∈ Finset.range 153, stT280 (i+1)) + stT280 154 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 153
    simpa using h
  have hprev := st280_p153
  have hstep := st280_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p155 : ((8334360226279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT280 (i+1))
      = (∑ i ∈ Finset.range 154, stT280 (i+1)) + stT280 155 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 154
    simpa using h
  have hprev := st280_p154
  have hstep := st280_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p156 : ((8305215292597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT280 (i+1))
      = (∑ i ∈ Finset.range 155, stT280 (i+1)) + stT280 156 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 155
    simpa using h
  have hprev := st280_p155
  have hstep := st280_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p157 : ((20395681578697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT280 (i+1))
      = (∑ i ∈ Finset.range 156, stT280 (i+1)) + stT280 157 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 156
    simpa using h
  have hprev := st280_p156
  have hstep := st280_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p158 : ((41245967498347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT280 (i+1))
      = (∑ i ∈ Finset.range 157, stT280 (i+1)) + stT280 158 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 157
    simpa using h
  have hprev := st280_p157
  have hstep := st280_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p159 : ((5224515255627/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT280 (i+1))
      = (∑ i ∈ Finset.range 158, stT280 (i+1)) + stT280 159 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 158
    simpa using h
  have hprev := st280_p158
  have hstep := st280_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p160 : ((20567837957083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT280 (i+1))
      = (∑ i ∈ Finset.range 159, stT280 (i+1)) + stT280 160 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 159
    simpa using h
  have hprev := st280_p159
  have hstep := st280_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p161 : ((4082273595073/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT280 (i+1))
      = (∑ i ∈ Finset.range 160, stT280 (i+1)) + stT280 161 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 160
    simpa using h
  have hprev := st280_p160
  have hstep := st280_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p162 : ((20792424579409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT280 (i+1))
      = (∑ i ∈ Finset.range 161, stT280 (i+1)) + stT280 162 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 161
    simpa using h
  have hprev := st280_p161
  have hstep := st280_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p163 : ((20828779983939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT280 (i+1))
      = (∑ i ∈ Finset.range 162, stT280 (i+1)) + stT280 163 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 162
    simpa using h
  have hprev := st280_p162
  have hstep := st280_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p164 : ((40877578815931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT280 (i+1))
      = (∑ i ∈ Finset.range 163, stT280 (i+1)) + stT280 164 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 163
    simpa using h
  have hprev := st280_p163
  have hstep := st280_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p165 : ((41016950977377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT280 (i+1))
      = (∑ i ∈ Finset.range 164, stT280 (i+1)) + stT280 165 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 164
    simpa using h
  have hprev := st280_p164
  have hstep := st280_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p166 : ((41758144733677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT280 (i+1))
      = (∑ i ∈ Finset.range 165, stT280 (i+1)) + stT280 166 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 165
    simpa using h
  have hprev := st280_p165
  have hstep := st280_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p167 : ((41448228221677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT280 (i+1))
      = (∑ i ∈ Finset.range 166, stT280 (i+1)) + stT280 167 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 166
    simpa using h
  have hprev := st280_p166
  have hstep := st280_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p168 : ((10193981112573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT280 (i+1))
      = (∑ i ∈ Finset.range 167, stT280 (i+1)) + stT280 168 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 167
    simpa using h
  have hprev := st280_p167
  have hstep := st280_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p169 : ((2575789193157/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT280 (i+1))
      = (∑ i ∈ Finset.range 168, stT280 (i+1)) + stT280 169 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 168
    simpa using h
  have hprev := st280_p168
  have hstep := st280_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p170 : ((163306974559/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT280 (i+1))
      = (∑ i ∈ Finset.range 169, stT280 (i+1)) + stT280 170 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 169
    simpa using h
  have hprev := st280_p169
  have hstep := st280_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p171 : ((2580109263109/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT280 (i+1))
      = (∑ i ∈ Finset.range 170, stT280 (i+1)) + stT280 171 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 170
    simpa using h
  have hprev := st280_p170
  have hstep := st280_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p172 : ((40760514857381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT280 (i+1))
      = (∑ i ∈ Finset.range 171, stT280 (i+1)) + stT280 172 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 171
    simpa using h
  have hprev := st280_p171
  have hstep := st280_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p173 : ((41341871344341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT280 (i+1))
      = (∑ i ∈ Finset.range 172, stT280 (i+1)) + stT280 173 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 172
    simpa using h
  have hprev := st280_p172
  have hstep := st280_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p174 : ((41804940345681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT280 (i+1))
      = (∑ i ∈ Finset.range 173, stT280 (i+1)) + stT280 174 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 173
    simpa using h
  have hprev := st280_p173
  have hstep := st280_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p175 : ((10297788113799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT280 (i+1))
      = (∑ i ∈ Finset.range 174, stT280 (i+1)) + stT280 175 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 174
    simpa using h
  have hprev := st280_p174
  have hstep := st280_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p176 : ((20383145476039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT280 (i+1))
      = (∑ i ∈ Finset.range 175, stT280 (i+1)) + stT280 176 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 175
    simpa using h
  have hprev := st280_p175
  have hstep := st280_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p177 : ((20696848692369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT280 (i+1))
      = (∑ i ∈ Finset.range 176, stT280 (i+1)) + stT280 177 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 176
    simpa using h
  have hprev := st280_p176
  have hstep := st280_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p178 : ((1306318165197/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT280 (i+1))
      = (∑ i ∈ Finset.range 177, stT280 (i+1)) + stT280 178 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 177
    simpa using h
  have hprev := st280_p177
  have hstep := st280_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p179 : ((10294090710043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT280 (i+1))
      = (∑ i ∈ Finset.range 178, stT280 (i+1)) + stT280 179 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 178
    simpa using h
  have hprev := st280_p178
  have hstep := st280_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p180 : ((10190486971399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT280 (i+1))
      = (∑ i ∈ Finset.range 179, stT280 (i+1)) + stT280 180 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 179
    simpa using h
  have hprev := st280_p179
  have hstep := st280_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p181 : ((20685779114907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT280 (i+1))
      = (∑ i ∈ Finset.range 180, stT280 (i+1)) + stT280 181 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 180
    simpa using h
  have hprev := st280_p180
  have hstep := st280_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p182 : ((41812495386207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT280 (i+1))
      = (∑ i ∈ Finset.range 181, stT280 (i+1)) + stT280 182 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 181
    simpa using h
  have hprev := st280_p181
  have hstep := st280_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p183 : ((41234736473113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT280 (i+1))
      = (∑ i ∈ Finset.range 182, stT280 (i+1)) + stT280 183 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 182
    simpa using h
  have hprev := st280_p182
  have hstep := st280_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p184 : ((40749374364943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT280 (i+1))
      = (∑ i ∈ Finset.range 183, stT280 (i+1)) + stT280 184 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 183
    simpa using h
  have hprev := st280_p183
  have hstep := st280_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p185 : ((8255250595881/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT280 (i+1))
      = (∑ i ∈ Finset.range 184, stT280 (i+1)) + stT280 185 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 184
    simpa using h
  have hprev := st280_p184
  have hstep := st280_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p186 : ((1045471043669/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT280 (i+1))
      = (∑ i ∈ Finset.range 185, stT280 (i+1)) + stT280 186 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 185
    simpa using h
  have hprev := st280_p185
  have hstep := st280_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p187 : ((10341428204987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT280 (i+1))
      = (∑ i ∈ Finset.range 186, stT280 (i+1)) + stT280 187 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 186
    simpa using h
  have hprev := st280_p186
  have hstep := st280_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p188 : ((2547497243503/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT280 (i+1))
      = (∑ i ∈ Finset.range 187, stT280 (i+1)) + stT280 188 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 187
    simpa using h
  have hprev := st280_p187
  have hstep := st280_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p189 : ((2569505124931/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT280 (i+1))
      = (∑ i ∈ Finset.range 188, stT280 (i+1)) + stT280 189 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 188
    simpa using h
  have hprev := st280_p188
  have hstep := st280_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p190 : ((326381029811/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT280 (i+1))
      = (∑ i ∈ Finset.range 189, stT280 (i+1)) + stT280 190 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 189
    simpa using h
  have hprev := st280_p189
  have hstep := st280_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p191 : ((10388796775527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT280 (i+1))
      = (∑ i ∈ Finset.range 190, stT280 (i+1)) + stT280 191 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 190
    simpa using h
  have hprev := st280_p190
  have hstep := st280_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p192 : ((10212053038841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT280 (i+1))
      = (∑ i ∈ Finset.range 191, stT280 (i+1)) + stT280 192 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 191
    simpa using h
  have hprev := st280_p191
  have hstep := st280_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p193 : ((20455097712507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT280 (i+1))
      = (∑ i ∈ Finset.range 192, stT280 (i+1)) + stT280 193 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 192
    simpa using h
  have hprev := st280_p192
  have hstep := st280_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p194 : ((520345160033/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT280 (i+1))
      = (∑ i ∈ Finset.range 193, stT280 (i+1)) + stT280 194 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 193
    simpa using h
  have hprev := st280_p193
  have hstep := st280_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p195 : ((4174780895697/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT280 (i+1))
      = (∑ i ∈ Finset.range 194, stT280 (i+1)) + stT280 195 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 194
    simpa using h
  have hprev := st280_p194
  have hstep := st280_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p196 : ((1026673520687/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT280 (i+1))
      = (∑ i ∈ Finset.range 195, stT280 (i+1)) + stT280 196 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 195
    simpa using h
  have hprev := st280_p195
  have hstep := st280_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p197 : ((20377505524543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT280 (i+1))
      = (∑ i ∈ Finset.range 196, stT280 (i+1)) + stT280 197 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 196
    simpa using h
  have hprev := st280_p196
  have hstep := st280_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p198 : ((41339023909237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT280 (i+1))
      = (∑ i ∈ Finset.range 197, stT280 (i+1)) + stT280 198 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 197
    simpa using h
  have hprev := st280_p197
  have hstep := st280_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p199 : ((41830627211689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT280 (i+1))
      = (∑ i ∈ Finset.range 198, stT280 (i+1)) + stT280 199 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 198
    simpa using h
  have hprev := st280_p198
  have hstep := st280_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p200 : ((20704977204071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT280 (i+1))
      = (∑ i ∈ Finset.range 199, stT280 (i+1)) + stT280 200 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 199
    simpa using h
  have hprev := st280_p199
  have hstep := st280_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p201 : ((20389391296751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT280 (i+1))
      = (∑ i ∈ Finset.range 200, stT280 (i+1)) + stT280 201 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 200
    simpa using h
  have hprev := st280_p200
  have hstep := st280_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p202 : ((8194853856077/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT280 (i+1))
      = (∑ i ∈ Finset.range 201, stT280 (i+1)) + stT280 202 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 201
    simpa using h
  have hprev := st280_p201
  have hstep := st280_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p203 : ((8334605810069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT280 (i+1))
      = (∑ i ∈ Finset.range 202, stT280 (i+1)) + stT280 203 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 202
    simpa using h
  have hprev := st280_p202
  have hstep := st280_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p204 : ((8348766701681/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT280 (i+1))
      = (∑ i ∈ Finset.range 203, stT280 (i+1)) + stT280 204 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 203
    simpa using h
  have hprev := st280_p203
  have hstep := st280_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p205 : ((10269293359041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT280 (i+1))
      = (∑ i ∈ Finset.range 204, stT280 (i+1)) + stT280 205 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 204
    simpa using h
  have hprev := st280_p204
  have hstep := st280_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p206 : ((5092034253897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT280 (i+1))
      = (∑ i ∈ Finset.range 205, stT280 (i+1)) + stT280 206 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 205
    simpa using h
  have hprev := st280_p205
  have hstep := st280_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p207 : ((80578097163/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT280 (i+1))
      = (∑ i ∈ Finset.range 206, stT280 (i+1)) + stT280 207 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 206
    simpa using h
  have hprev := st280_p206
  have hstep := st280_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p208 : ((41818930669581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT280 (i+1))
      = (∑ i ∈ Finset.range 207, stT280 (i+1)) + stT280 208 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 207
    simpa using h
  have hprev := st280_p207
  have hstep := st280_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p209 : ((20776210244473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT280 (i+1))
      = (∑ i ∈ Finset.range 208, stT280 (i+1)) + stT280 209 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 208
    simpa using h
  have hprev := st280_p208
  have hstep := st280_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p210 : ((4087126600127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT280 (i+1))
      = (∑ i ∈ Finset.range 209, stT280 (i+1)) + stT280 210 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 209
    simpa using h
  have hprev := st280_p209
  have hstep := st280_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p211 : ((40816604050241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT280 (i+1))
      = (∑ i ∈ Finset.range 210, stT280 (i+1)) + stT280 211 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 210
    simpa using h
  have hprev := st280_p210
  have hstep := st280_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p212 : ((41467118866571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT280 (i+1))
      = (∑ i ∈ Finset.range 211, stT280 (i+1)) + stT280 212 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 211
    simpa using h
  have hprev := st280_p211
  have hstep := st280_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p213 : ((41842301093039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT280 (i+1))
      = (∑ i ∈ Finset.range 212, stT280 (i+1)) + stT280 213 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 212
    simpa using h
  have hprev := st280_p212
  have hstep := st280_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p214 : ((41385393577811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT280 (i+1))
      = (∑ i ∈ Finset.range 213, stT280 (i+1)) + stT280 214 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 213
    simpa using h
  have hprev := st280_p213
  have hstep := st280_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p215 : ((40776252011691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT280 (i+1))
      = (∑ i ∈ Finset.range 214, stT280 (i+1)) + stT280 215 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 214
    simpa using h
  have hprev := st280_p214
  have hstep := st280_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p216 : ((40908102442831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT280 (i+1))
      = (∑ i ∈ Finset.range 215, stT280 (i+1)) + stT280 216 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 215
    simpa using h
  have hprev := st280_p215
  have hstep := st280_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p217 : ((41584607146407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT280 (i+1))
      = (∑ i ∈ Finset.range 216, stT280 (i+1)) + stT280 217 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 216
    simpa using h
  have hprev := st280_p216
  have hstep := st280_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p218 : ((10456721553473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT280 (i+1))
      = (∑ i ∈ Finset.range 217, stT280 (i+1)) + stT280 218 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 217
    simpa using h
  have hprev := st280_p217
  have hstep := st280_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p219 : ((10322760549401/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT280 (i+1))
      = (∑ i ∈ Finset.range 218, stT280 (i+1)) + stT280 219 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 218
    simpa using h
  have hprev := st280_p218
  have hstep := st280_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p220 : ((10185614448301/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT280 (i+1))
      = (∑ i ∈ Finset.range 219, stT280 (i+1)) + stT280 220 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 219
    simpa using h
  have hprev := st280_p219
  have hstep := st280_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p221 : ((10238423572669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT280 (i+1))
      = (∑ i ∈ Finset.range 220, stT280 (i+1)) + stT280 221 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 220
    simpa using h
  have hprev := st280_p220
  have hstep := st280_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p222 : ((10406190424521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT280 (i+1))
      = (∑ i ∈ Finset.range 221, stT280 (i+1)) + stT280 222 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 221
    simpa using h
  have hprev := st280_p221
  have hstep := st280_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p223 : ((20911180192853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT280 (i+1))
      = (∑ i ∈ Finset.range 222, stT280 (i+1)) + stT280 223 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 222
    simpa using h
  have hprev := st280_p222
  have hstep := st280_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p224 : ((10319398429183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT280 (i+1))
      = (∑ i ∈ Finset.range 223, stT280 (i+1)) + stT280 224 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 223
    simpa using h
  have hprev := st280_p223
  have hstep := st280_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p225 : ((5092342180913/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT280 (i+1))
      = (∑ i ∈ Finset.range 224, stT280 (i+1)) + stT280 225 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 224
    simpa using h
  have hprev := st280_p224
  have hstep := st280_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p226 : ((20467808528777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT280 (i+1))
      = (∑ i ∈ Finset.range 225, stT280 (i+1)) + stT280 226 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 225
    simpa using h
  have hprev := st280_p225
  have hstep := st280_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p227 : ((162495788719/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT280 (i+1))
      = (∑ i ∈ Finset.range 226, stT280 (i+1)) + stT280 227 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 226
    simpa using h
  have hprev := st280_p226
  have hstep := st280_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p228 : ((20920446689109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT280 (i+1))
      = (∑ i ∈ Finset.range 227, stT280 (i+1)) + stT280 228 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 227
    simpa using h
  have hprev := st280_p227
  have hstep := st280_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p229 : ((10335957322833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT280 (i+1))
      = (∑ i ∈ Finset.range 228, stT280 (i+1)) + stT280 229 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 228
    simpa using h
  have hprev := st280_p228
  have hstep := st280_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p230 : ((40765311480267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT280 (i+1))
      = (∑ i ∈ Finset.range 229, stT280 (i+1)) + stT280 230 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 229
    simpa using h
  have hprev := st280_p229
  have hstep := st280_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p231 : ((40860030106227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT280 (i+1))
      = (∑ i ∈ Finset.range 230, stT280 (i+1)) + stT280 231 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 230
    simpa using h
  have hprev := st280_p230
  have hstep := st280_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p232 : ((41501161178571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT280 (i+1))
      = (∑ i ∈ Finset.range 231, stT280 (i+1)) + stT280 232 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 231
    simpa using h
  have hprev := st280_p231
  have hstep := st280_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p233 : ((41861948105449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT280 (i+1))
      = (∑ i ∈ Finset.range 232, stT280 (i+1)) + stT280 233 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 232
    simpa using h
  have hprev := st280_p232
  have hstep := st280_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p234 : ((5185534969451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT280 (i+1))
      = (∑ i ∈ Finset.range 233, stT280 (i+1)) + stT280 234 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 233
    simpa using h
  have hprev := st280_p233
  have hstep := st280_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p235 : ((5106309612401/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT280 (i+1))
      = (∑ i ∈ Finset.range 234, stT280 (i+1)) + stT280 235 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 234
    simpa using h
  have hprev := st280_p234
  have hstep := st280_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p236 : ((20378926967579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT280 (i+1))
      = (∑ i ∈ Finset.range 235, stT280 (i+1)) + stT280 236 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 235
    simpa using h
  have hprev := st280_p235
  have hstep := st280_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p237 : ((41318406648967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT280 (i+1))
      = (∑ i ∈ Finset.range 236, stT280 (i+1)) + stT280 237 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 236
    simpa using h
  have hprev := st280_p236
  have hstep := st280_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p238 : ((2091732780623/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT280 (i+1))
      = (∑ i ∈ Finset.range 237, stT280 (i+1)) + stT280 238 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 237
    simpa using h
  have hprev := st280_p237
  have hstep := st280_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p239 : ((5209123481007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT280 (i+1))
      = (∑ i ∈ Finset.range 238, stT280 (i+1)) + stT280 239 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 238
    simpa using h
  have hprev := st280_p238
  have hstep := st280_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p240 : ((20517310977729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT280 (i+1))
      = (∑ i ∈ Finset.range 239, stT280 (i+1)) + stT280 240 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 239
    simpa using h
  have hprev := st280_p239
  have hstep := st280_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p241 : ((40694782114497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT280 (i+1))
      = (∑ i ∈ Finset.range 240, stT280 (i+1)) + stT280 241 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 240
    simpa using h
  have hprev := st280_p240
  have hstep := st280_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p242 : ((8211939702869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT280 (i+1))
      = (∑ i ∈ Finset.range 241, stT280 (i+1)) + stT280 242 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 241
    simpa using h
  have hprev := st280_p241
  have hstep := st280_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p243 : ((8337982649269/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT280 (i+1))
      = (∑ i ∈ Finset.range 242, stT280 (i+1)) + stT280 243 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 242
    simpa using h
  have hprev := st280_p242
  have hstep := st280_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p244 : ((8367578355589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT280 (i+1))
      = (∑ i ∈ Finset.range 243, stT280 (i+1)) + stT280 244 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 243
    simpa using h
  have hprev := st280_p243
  have hstep := st280_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p245 : ((20666364908707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT280 (i+1))
      = (∑ i ∈ Finset.range 244, stT280 (i+1)) + stT280 245 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 244
    simpa using h
  have hprev := st280_p244
  have hstep := st280_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p246 : ((8153529447009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT280 (i+1))
      = (∑ i ∈ Finset.range 245, stT280 (i+1)) + stT280 246 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 245
    simpa using h
  have hprev := st280_p245
  have hstep := st280_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p247 : ((40797334973917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT280 (i+1))
      = (∑ i ∈ Finset.range 246, stT280 (i+1)) + stT280 247 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 246
    simpa using h
  have hprev := st280_p246
  have hstep := st280_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p248 : ((41383951783917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT280 (i+1))
      = (∑ i ∈ Finset.range 247, stT280 (i+1)) + stT280 248 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 247
    simpa using h
  have hprev := st280_p247
  have hstep := st280_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p249 : ((41854465871233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT280 (i+1))
      = (∑ i ∈ Finset.range 248, stT280 (i+1)) + stT280 249 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 248
    simpa using h
  have hprev := st280_p248
  have hstep := st280_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_p250 : ((41676335271289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT280 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT280 (i+1))
      = (∑ i ∈ Finset.range 249, stT280 (i+1)) + stT280 250 := by
    have h := Finset.sum_range_succ (fun i => stT280 (i+1)) 249
    simpa using h
  have hprev := st280_p249
  have hstep := st280_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st280_s250 :
    |Real.sin (((280 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))
      - ((239883/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 4640641/10000000) (δ := 2807/200000000) (ψ := -188847/125000) 280 246
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 280`** (evaluated boundary). -/
theorem station_280_sign : hardyG ((((280:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 280 250 (by norm_num) (by norm_num)
    ((-188847/125000 : ℚ) : ℝ)
  have hchain := st280_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT280 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((280 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-188847/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st280_c250
  have hsinb := abs_le.mp st280_s250
  have hbdy_lo : ((-42460279118147/784002500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((280 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-188847/125000 : ℚ) : ℝ))) / 2
          - ((((280:ℕ)):ℝ))
            * Real.sin (((280 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-188847/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((280:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((280:ℝ) * Real.log (250:ℝ) - ((-188847/125000 : ℚ) : ℝ))) / 2
        - ((280:ℝ)) * Real.sin ((280:ℝ) * Real.log (250:ℝ) - ((-188847/125000 : ℚ) : ℝ))
        ≥ ((-537084371/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((280:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-537084371/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-537084371/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-537084371/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((280:ℕ)):ℝ))+1) * (((((280:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((535067341897/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((41676335271289/10000000000000 : ℚ) : ℝ) + ((-42460279118147/784002500000000 : ℚ) : ℝ)
      - ((535067341897/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-188847/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((280:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-188847/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((280:ℕ)):ℝ)))).re
      - Real.sin ((-188847/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((280:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((280:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((280:ℕ)):ℝ))
      = (((((280:ℕ)):ℝ)) * (Real.log ((((280:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((280:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_280
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
  have hθwin : |(((-188847/125000 : ℚ) : ℝ) + ((63:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((280:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((280:ℕ)):ℝ)))
    (φ := ((-188847/125000 : ℚ) : ℝ) + ((63:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-188847/125000 : ℚ) : ℝ) + ((63:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-188847/125000 : ℚ)) : ℝ) - Real.pi) + ((63:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-188847/125000 : ℚ)) : ℝ) - Real.pi) 63).1,
    (cos_sin_shift ((((-188847/125000 : ℚ)) : ℝ) - Real.pi) 63).2]
  exact cos_sin_flip ((-188847/125000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_280_sign
end AxiomAudit
