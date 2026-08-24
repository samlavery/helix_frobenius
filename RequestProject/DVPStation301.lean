import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 301` (rung-309; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT301 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((301 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))

theorem st301_c1 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((100907/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1302441/5000000) (δ := 201/1000000000) (ψ := 1041953/1000000) 301 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t1 : ((100887/200000 : ℚ) : ℝ) ≤ stT301 1 := by
  have hc : ((100887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100887/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((100887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c2 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((968857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15639/250000) (δ := 3013/200000000) (ψ := 1041953/1000000) 301 33
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t2 : ((6850145653719/10000000000000 : ℚ) : ℝ) ≤ stT301 2 := by
  have hc : ((968757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6850145653719/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((968757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c3 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-97437/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3643373/5000000) (δ := 607/40000000) (ψ := 1041953/1000000) 301 52
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t3 : ((-562610546841/1000000000000 : ℚ) : ℝ) ≤ stT301 3 := by
  have hc : ((-97447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562610546841/1000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-97447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c4 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((28377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96401/250000) (δ := 1891/125000000) (ψ := 1041953/1000000) 301 66
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t4 : ((28277/2000000 : ℚ) : ℝ) ≤ stT301 4 := by
  have hc : ((28277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28277/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((28277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c5 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((18371/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1015997/10000000) (δ := 15149/1000000000) (ψ := 1041953/1000000) 301 77
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t5 : ((16429729563/40000000000 : ℚ) : ℝ) ≤ stT301 5 := by
  have hc : ((18369/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16429729563/40000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((18369/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c6 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-121061/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5190737/10000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 86
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t6 : ((-247165768269/1250000000000 : ℚ) : ℝ) ≤ stT301 6 := by
  have hc : ((-60543/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247165768269/1250000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-60543/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c7 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((471249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 851921/10000000) (δ := 7617/500000000) (ψ := 1041953/1000000) 301 93
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t7 : ((445241118289/1250000000000 : ℚ) : ℝ) ≤ stT301 7 := by
  have hc : ((471199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445241118289/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((471199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c8 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-953249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177163/250000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 99
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t8 : ((-1685298901683/5000000000000 : ℚ) : ℝ) ≤ stT301 8 := by
  have hc : ((-953349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1685298901683/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-953349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c9 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((51997/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91903/625000) (δ := 3787/250000000) (ψ := 1041953/1000000) 301 105
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t9 : ((693209930679/2500000000000 : ℚ) : ℝ) ≤ stT301 9 := by
  have hc : ((207963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((693209930679/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((207963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c10 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((632699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276801/1250000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 110
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t10 : ((2000453267923/10000000000000 : ℚ) : ℝ) ≤ stT301 10 := by
  have hc : ((632599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2000453267923/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((632599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c11 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-66923/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4604483/10000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 115
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t11 : ((-25231981509/312500000000 : ℚ) : ℝ) ≤ stT301 11 := by
  have hc : ((-16737/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25231981509/312500000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-16737/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c12 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((354011/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1960257/10000000) (δ := 3789/250000000) (ψ := 1041953/1000000) 301 119
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t12 : ((1021797270711/5000000000000 : ℚ) : ℝ) ≤ stT301 12 := by
  have hc : ((353961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1021797270711/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((353961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c13 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-250499/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4559979/10000000) (δ := 7609/500000000) (ψ := 1041953/1000000) 301 123
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t13 : ((-695036577099/10000000000000 : ℚ) : ℝ) ≤ stT301 13 := by
  have hc : ((-250599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-695036577099/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-250599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c14 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-15531/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2041201/5000000) (δ := 7603/500000000) (ψ := 1041953/1000000) 301 126
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t14 : ((-10393791957/625000000000 : ℚ) : ℝ) ≤ stT301 14 := by
  have hc : ((-3889/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10393791957/625000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-3889/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c15 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-57353/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3416147/5000000) (δ := 3027/200000000) (ψ := 1041953/1000000) 301 130
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t15 : ((-592403810193/2500000000000 : ℚ) : ℝ) ≤ stT301 15 := by
  have hc : ((-229437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592403810193/2500000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-229437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c16 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-55269/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5390963/10000000) (δ := 15147/1000000000) (ψ := 1041953/1000000) 301 133
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t16 : ((-138197555279/1000000000000 : ℚ) : ℝ) ≤ stT301 16 := by
  have hc : ((-55279/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138197555279/1000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-55279/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c17 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-463651/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6894841/10000000) (δ := 7539/500000000) (ψ := 1041953/1000000) 301 136
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t17 : ((-1124640466257/5000000000000 : ℚ) : ℝ) ≤ stT301 17 := by
  have hc : ((-463701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1124640466257/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-463701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c18 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-152327/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36726/78125) (δ := 15211/1000000000) (ψ := 1041953/1000000) 301 138
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t18 : ((-359156093671/5000000000000 : ℚ) : ℝ) ≤ stT301 18 := by
  have hc : ((-152377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-359156093671/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-152377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c19 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((768081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1737393/10000000) (δ := 7607/500000000) (ψ := 1041953/1000000) 301 141
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t19 : ((1761868987017/10000000000000 : ℚ) : ℝ) ≤ stT301 19 := by
  have hc : ((767981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1761868987017/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((767981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c20 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-71317/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680611/1250000) (δ := 607/40000000) (ψ := 1041953/1000000) 301 143
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t20 : ((-79748806203/625000000000 : ℚ) : ℝ) ≤ stT301 20 := by
  have hc : ((-142659/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79748806203/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-142659/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c21 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-100787/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -620547/1250000) (δ := 15053/1000000000) (ψ := 1041953/1000000) 301 146
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t21 : ((-54997457337/625000000000 : ℚ) : ℝ) ≤ stT301 21 := by
  have hc : ((-25203/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54997457337/625000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-25203/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c22 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((852733/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1374003/10000000) (δ := 15239/1000000000) (ψ := 1041953/1000000) 301 148
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t22 : ((1817819524431/10000000000000 : ℚ) : ℝ) ≤ stT301 22 := by
  have hc : ((852633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1817819524431/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((852633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c23 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((965349/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13201/200000) (δ := 609/40000000) (ψ := 1041953/1000000) 301 150
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t23 : ((251585395107/1250000000000 : ℚ) : ℝ) ≤ stT301 23 := by
  have hc : ((965249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251585395107/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((965249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c24 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((218419/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1270223/10000000) (δ := 15093/1000000000) (ψ := 1041953/1000000) 301 152
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t24 : ((222897393477/1250000000000 : ℚ) : ℝ) ≤ stT301 24 := by
  have hc : ((109197/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222897393477/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((109197/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c25 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((486931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 572851/10000000) (δ := 3799/250000000) (ψ := 1041953/1000000) 301 154
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t25 : ((486881/2500000 : ℚ) : ℝ) ≤ stT301 25 := by
  have hc : ((486881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486881/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((486881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c26 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((107737/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -664749/5000000) (δ := 7611/500000000) (ψ := 1041953/1000000) 301 156
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t26 : ((422530176289/2500000000000 : ℚ) : ℝ) ≤ stT301 26 := by
  have hc : ((215449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422530176289/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((215449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c27 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-166761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4345849/10000000) (δ := 473/31250000) (ψ := 1041953/1000000) 301 158
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t27 : ((-321124161361/10000000000000 : ℚ) : ℝ) ≤ stT301 27 := by
  have hc : ((-166861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321124161361/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-166861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c28 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-244167/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3656441/5000000) (δ := 15143/1000000000) (ψ := 1041953/1000000) 301 159
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t28 : ((-14421239313/78125000000 : ℚ) : ℝ) ≤ stT301 28 := by
  have hc : ((-15262/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14421239313/78125000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-15262/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c29 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((120963/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1151579/5000000) (δ := 7623/500000000) (ψ := 1041953/1000000) 301 161
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t29 : ((224585466679/2000000000000 : ℚ) : ℝ) ≤ stT301 29 := by
  have hc : ((120943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224585466679/2000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((120943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c30 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((5187/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3601889/10000000) (δ := 3793/250000000) (ψ := 1041953/1000000) 301 163
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t30 : ((9462815603/400000000000 : ℚ) : ℝ) ≤ stT301 30 := by
  have hc : ((5183/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9462815603/400000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((5183/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c31 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-271927/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5364547/10000000) (δ := 3781/250000000) (ψ := 1041953/1000000) 301 164
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t31 : ((-244242689379/2500000000000 : ℚ) : ℝ) ≤ stT301 31 := by
  have hc : ((-271977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244242689379/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-271977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c32 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((324627/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2160483/10000000) (δ := 1521/100000000) (ψ := 1041953/1000000) 301 166
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t32 : ((286888092491/2500000000000 : ℚ) : ℝ) ≤ stT301 32 := by
  have hc : ((324577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286888092491/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((324577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c33 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-129407/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5287183/10000000) (δ := 15103/1000000000) (ψ := 1041953/1000000) 301 167
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t33 : ((-28164031083/312500000000 : ℚ) : ℝ) ≤ stT301 33 := by
  have hc : ((-16179/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28164031083/312500000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-16179/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c34 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((104859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3664361/10000000) (δ := 943/62500000) (ψ := 1041953/1000000) 301 169
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t34 : ((35932022723/2000000000000 : ℚ) : ℝ) ≤ stT301 34 := by
  have hc : ((104759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35932022723/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((104759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c35 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((112017/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 244077/1000000) (δ := 7611/500000000) (ψ := 1041953/1000000) 301 170
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t35 : ((47327356269/500000000000 : ℚ) : ℝ) ≤ stT301 35 := by
  have hc : ((111997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47327356269/500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((111997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c36 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-6247/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1555311/2000000) (δ := 15167/1000000000) (ψ := 1041953/1000000) 301 172
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t36 : ((-83301683327/500000000000 : ℚ) : ℝ) ≤ stT301 36 := by
  have hc : ((-49981/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83301683327/500000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-49981/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c37 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((41149/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -286677/1000000) (δ := 3811/250000000) (ψ := 1041953/1000000) 301 173
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t37 : ((67632063471/1000000000000 : ℚ) : ℝ) ≤ stT301 37 := by
  have hc : ((41139/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67632063471/1000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((41139/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c38 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((413447/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493087/10000000) (δ := 15151/1000000000) (ψ := 1041953/1000000) 301 174
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t38 : ((335309200479/2500000000000 : ℚ) : ℝ) ≤ stT301 38 := by
  have hc : ((413397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335309200479/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((413397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c39 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-532777/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5331687/10000000) (δ := 3029/200000000) (ψ := 1041953/1000000) 301 175
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t39 : ((-426643174157/5000000000000 : ℚ) : ℝ) ≤ stT301 39 := by
  have hc : ((-532877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426643174157/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-532877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c40 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-94651/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406519/2000000) (δ := 15131/1000000000) (ψ := 1041953/1000000) 301 177
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t40 : ((-149672198879/1000000000000 : ℚ) : ℝ) ≤ stT301 40 := by
  have hc : ((-94661/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149672198879/1000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-94661/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c41 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-92821/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4159377/10000000) (δ := 1903/125000000) (ψ := 1041953/1000000) 301 178
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t41 : ((-72559128349/5000000000000 : ℚ) : ℝ) ≤ stT301 41 := by
  have hc : ((-92921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72559128349/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-92921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c42 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((48061/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216737/1250000) (δ := 3779/250000000) (ψ := 1041953/1000000) 301 179
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t42 : ((296600260227/2500000000000 : ℚ) : ℝ) ≤ stT301 42 := by
  have hc : ((192219/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296600260227/2500000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((192219/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c43 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((497197/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132421/5000000) (δ := 15109/1000000000) (ψ := 1041953/1000000) 301 180
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t43 : ((151628343559/1000000000000 : ℚ) : ℝ) ≤ stT301 43 := by
  have hc : ((497147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151628343559/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((497147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c44 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((736719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 928239/5000000) (δ := 15201/1000000000) (ψ := 1041953/1000000) 301 181
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t44 : ((277623598291/2500000000000 : ℚ) : ℝ) ≤ stT301 44 := by
  have hc : ((736619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277623598291/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((736619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c45 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((340151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95603/312500) (δ := 3039/200000000) (ψ := 1041953/1000000) 301 182
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t45 : ((506917766261/10000000000000 : ℚ) : ℝ) ≤ stT301 45 := by
  have hc : ((340051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506917766261/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((340051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c46 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((7307/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778091/2000000) (δ := 3797/250000000) (ψ := 1041953/1000000) 301 183
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t46 : ((10699858683/5000000000000 : ℚ) : ℝ) ≤ stT301 46 := by
  have hc : ((7257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10699858683/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((7257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c47 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-21837/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4365983/10000000) (δ := 15123/1000000000) (ψ := 1041953/1000000) 301 184
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t47 : ((-1274830927/50000000000 : ℚ) : ℝ) ≤ stT301 47 := by
  have hc : ((-43699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1274830927/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-43699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c48 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-56869/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4500703/10000000) (δ := 15073/1000000000) (ψ := 1041953/1000000) 301 185
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t48 : ((-2566232317/78125000000 : ℚ) : ℝ) ≤ stT301 48 := by
  have hc : ((-28447/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2566232317/78125000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-28447/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c49 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-76043/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269293/625000) (δ := 15137/1000000000) (ψ := 1041953/1000000) 301 186
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t49 : ((-27176082299/1250000000000 : ℚ) : ℝ) ≤ stT301 49 := by
  have hc : ((-76093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27176082299/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-76093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c50 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((49443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 950833/2500000) (δ := 3811/250000000) (ψ := 1041953/1000000) 301 187
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t50 : ((69781512059/10000000000000 : ℚ) : ℝ) ≤ stT301 50 := by
  have hc : ((49343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69781512059/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((49343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c51 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((363541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119873/400000) (δ := 15151/1000000000) (ψ := 1041953/1000000) 301 188
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t51 : ((12722979087/250000000000 : ℚ) : ℝ) ≤ stT301 51 := by
  have hc : ((363441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12722979087/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((363441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c52 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((144913/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 950491/5000000) (δ := 7579/500000000) (ψ := 1041953/1000000) 301 189
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t52 : ((803721471/8000000000 : ℚ) : ℝ) ≤ stT301 52 := by
  have hc : ((144893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((803721471/8000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((144893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c53 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((977881/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 526789/10000000) (δ := 7533/500000000) (ψ := 1041953/1000000) 301 190
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t53 : ((268616974101/2000000000000 : ℚ) : ℝ) ≤ stT301 53 := by
  have hc : ((977781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268616974101/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((977781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c54 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((225529/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1115369/10000000) (δ := 15073/1000000000) (ψ := 1041953/1000000) 301 191
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t54 : ((9589747869/78125000000 : ℚ) : ℝ) ≤ stT301 54 := by
  have hc : ((14094/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9589747869/78125000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((14094/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c55 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((178261/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -603127/2000000) (δ := 15223/1000000000) (ψ := 1041953/1000000) 301 192
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t55 : ((240299534189/5000000000000 : ℚ) : ℝ) ≤ stT301 55 := by
  have hc : ((178211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240299534189/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((178211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c56 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-475097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5164677/10000000) (δ := 951/62500000) (ψ := 1041953/1000000) 301 193
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t56 : ((-635009077479/10000000000000 : ℚ) : ℝ) ≤ stT301 56 := by
  have hc : ((-475197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-635009077479/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-475197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c57 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-198559/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7553691/10000000) (δ := 15109/1000000000) (ψ := 1041953/1000000) 301 194
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t57 : ((-263024438607/2000000000000 : ℚ) : ℝ) ≤ stT301 57 := by
  have hc : ((-198579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263024438607/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-198579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c58 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-299663/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5533639/10000000) (δ := 7597/500000000) (ψ := 1041953/1000000) 301 194
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t58 : ((-78708530069/1000000000000 : ℚ) : ℝ) ≤ stT301 58 := by
  have hc : ((-299713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78708530069/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-299713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c59 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((47513/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2689211/10000000) (δ := 15201/1000000000) (ψ := 1041953/1000000) 301 195
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t59 : ((61843633167/1000000000000 : ℚ) : ℝ) ≤ stT301 59 := by
  have hc : ((47503/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61843633167/1000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((47503/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c60 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((197797/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371409/10000000) (δ := 15109/1000000000) (ψ := 1041953/1000000) 301 196
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t60 : ((127664460169/1000000000000 : ℚ) : ℝ) ≤ stT301 60 := by
  have hc : ((197777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127664460169/1000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((197777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c61 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((57059/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1820537/5000000) (δ := 3779/250000000) (ψ := 1041953/1000000) 301 197
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t61 : ((4562031207/312500000000 : ℚ) : ℝ) ≤ stT301 61 := by
  have hc : ((57009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4562031207/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((57009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c62 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-478199/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7113011/10000000) (δ := 15123/1000000000) (ψ := 1041953/1000000) 301 198
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t62 : ((-303688593249/2500000000000 : ℚ) : ℝ) ≤ stT301 62 := by
  have hc : ((-478249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303688593249/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-478249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c63 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-389529/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 492729/1000000) (δ := 15123/1000000000) (ψ := 1041953/1000000) 301 198
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t63 : ((-245443281889/5000000000000 : ℚ) : ℝ) ≤ stT301 63 := by
  have hc : ((-389629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245443281889/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-389629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c64 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((909811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534961/5000000) (δ := 15173/1000000000) (ψ := 1041953/1000000) 301 199
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t64 : ((909711/8000000 : ℚ) : ℝ) ≤ stT301 64 := by
  have hc : ((909711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((909711/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((909711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c65 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((373097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297113/1000000) (δ := 15237/1000000000) (ψ := 1041953/1000000) 301 200
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t65 : ((462645709959/10000000000000 : ℚ) : ℝ) ≤ stT301 65 := by
  have hc : ((372997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462645709959/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((372997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c66 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-964969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71903/100000) (δ := 7529/500000000) (ψ := 1041953/1000000) 301 201
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t66 : ((-237583581627/2000000000000 : ℚ) : ℝ) ≤ stT301 66 := by
  have hc : ((-965069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237583581627/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-965069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c67 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-4963/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103143/250000) (δ := 3029/200000000) (ψ := 1041953/1000000) 301 201
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t67 : ((-4856726303/500000000000 : ℚ) : ℝ) ≤ stT301 67 := by
  have hc : ((-19877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4856726303/500000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-19877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c68 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((492489/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -433881/10000000) (δ := 15151/1000000000) (ψ := 1041953/1000000) 301 202
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t68 : ((298584970821/2500000000000 : ℚ) : ℝ) ≤ stT301 68 := by
  have hc : ((492439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298584970821/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((492439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c69 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-472127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5156247/10000000) (δ := 15059/1000000000) (ψ := 1041953/1000000) 301 203
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t69 : ((-568494723993/10000000000000 : ℚ) : ℝ) ≤ stT301 69 := by
  have hc : ((-472227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568494723993/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-472227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c70 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-32123/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4537/8000) (δ := 15159/1000000000) (ψ := 1041953/1000000) 301 203
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t70 : ((-300002479/3906250000 : ℚ) : ℝ) ≤ stT301 70 := by
  have hc : ((-2008/3125 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300002479/3906250000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-2008/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c71 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((483847/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318599/5000000) (δ := 7533/500000000) (ψ := 1041953/1000000) 301 204
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t71 : ((574161087457/5000000000000 : ℚ) : ℝ) ≤ stT301 71 := by
  have hc : ((483797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((574161087457/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((483797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c72 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-245111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181843/400000) (δ := 1523/100000000) (ψ := 1041953/1000000) 301 205
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t72 : ((-18061506627/625000000000 : ℚ) : ℝ) ≤ stT301 72 := by
  have hc : ((-245211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18061506627/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-245211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c73 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-690773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729173/1250000) (δ := 15173/1000000000) (ψ := 1041953/1000000) 301 205
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t73 : ((-202151512419/2500000000000 : ℚ) : ℝ) ≤ stT301 73 := by
  have hc : ((-690873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202151512419/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-690873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c74 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((3092/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181817/5000000) (δ := 15223/1000000000) (ψ := 1041953/1000000) 301 206
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t74 : ((14376050073/125000000000 : ℚ) : ℝ) ≤ stT301 74 := by
  have hc : ((49467/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14376050073/125000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((49467/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c75 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-502581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2621723/5000000) (δ := 943/62500000) (ψ := 1041953/1000000) 301 207
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t75 : ((-580446253381/10000000000000 : ℚ) : ℝ) ≤ stT301 75 := by
  have hc : ((-502681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580446253381/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-502681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c76 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-156633/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4723567/10000000) (δ := 943/62500000) (ψ := 1041953/1000000) 301 207
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t76 : ((-179727778957/5000000000000 : ℚ) : ℝ) ≤ stT301 76 := by
  have hc : ((-156683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179727778957/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-156683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c77 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((896471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1147641/10000000) (δ := 3019/200000000) (ψ := 1041953/1000000) 301 208
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t77 : ((204301774691/2000000000000 : ℚ) : ℝ) ≤ stT301 77 := by
  have hc : ((896371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204301774691/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((896371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c78 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-192029/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1786449/2500000) (δ := 15101/1000000000) (ψ := 1041953/1000000) 301 209
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t78 : ((-108726428811/1000000000000 : ℚ) : ℝ) ≤ stT301 78 := by
  have hc : ((-192049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108726428811/1000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-192049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c79 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((7003/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1220151/5000000) (δ := 7601/500000000) (ψ := 1041953/1000000) 301 209
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t79 : ((31510311609/500000000000 : ℚ) : ℝ) ≤ stT301 79 := by
  have hc : ((28007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31510311609/500000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((28007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c80 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((4993/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760423/2000000) (δ := 7597/500000000) (ψ := 1041953/1000000) 301 210
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t80 : ((5571158439/1000000000000 : ℚ) : ℝ) ≤ stT301 80 := by
  have hc : ((4983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5571158439/1000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((4983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c81 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-603219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5545817/10000000) (δ := 15209/1000000000) (ψ := 1041953/1000000) 301 210
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t81 : ((-83794372591/1250000000000 : ℚ) : ℝ) ≤ stT301 81 := by
  have hc : ((-603319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83794372591/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-603319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c82 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((931763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7257/78125) (δ := 951/62500000) (ψ := 1041953/1000000) 301 211
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t82 : ((205769885169/2000000000000 : ℚ) : ℝ) ≤ stT301 82 := by
  have hc : ((931663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205769885169/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((931663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c83 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-990849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3757753/5000000) (δ := 3781/250000000) (ψ := 1041953/1000000) 301 212
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t83 : ((-1087708233207/10000000000000 : ℚ) : ℝ) ≤ stT301 83 := by
  have hc : ((-990949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1087708233207/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-990949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c84 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((165223/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1496547/10000000) (δ := 1889/62500000) (ψ := 1041953/1000000) 301 212
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t84 : ((180251176067/2000000000000 : ℚ) : ℝ) ≤ stT301 84 := by
  have hc : ((165203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180251176067/2000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((165203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c85 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-524051/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5305993/10000000) (δ := 471/31250000) (ψ := 1041953/1000000) 301 213
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t85 : ((-568521954603/10000000000000 : ℚ) : ℝ) ≤ stT301 85 := by
  have hc : ((-524151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568521954603/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-524151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c86 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((537/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3495247/10000000) (δ := 471/31250000) (ψ := 1041953/1000000) 301 213
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t86 : ((9259593949/500000000000 : ℚ) : ℝ) ≤ stT301 86 := by
  have hc : ((8587/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9259593949/500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((8587/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c87 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((82393/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3513139/10000000) (δ := 3013/200000000) (ψ := 1041953/1000000) 301 214
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t87 : ((5517557401/312500000000 : ℚ) : ℝ) ≤ stT301 87 := by
  have hc : ((82343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5517557401/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((82343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c88 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-447517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2543479/5000000) (δ := 7569/500000000) (ψ := 1041953/1000000) 301 214
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t88 : ((-119290378117/2500000000000 : ℚ) : ℝ) ≤ stT301 88 := by
  have hc : ((-447617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119290378117/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-447617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c89 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((132409/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529533/2500000) (δ := 7579/500000000) (ψ := 1041953/1000000) 301 215
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t89 : ((140331942833/2000000000000 : ℚ) : ℝ) ≤ stT301 89 := by
  have hc : ((132389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140331942833/2000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((132389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c90 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-202641/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6289777/10000000) (δ := 3049/200000000) (ψ := 1041953/1000000) 301 215
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t90 : ((-106814405969/1250000000000 : ℚ) : ℝ) ≤ stT301 90 := by
  have hc : ((-101333/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106814405969/1250000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-101333/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c91 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((90421/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44127/400000) (δ := 30251/1000000000) (ψ := 1041953/1000000) 301 216
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t91 : ((23694101181/250000000000 : ℚ) : ℝ) ≤ stT301 91 := by
  have hc : ((90411/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23694101181/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((90411/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c92 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-957319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1424187/2000000) (δ := 15251/1000000000) (ψ := 1041953/1000000) 301 216
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t92 : ((-998179199087/10000000000000 : ℚ) : ℝ) ≤ stT301 92 := by
  have hc : ((-957419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-998179199087/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-957419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c93 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((983713/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225913/5000000) (δ := 3811/250000000) (ψ := 1041953/1000000) 301 217
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t93 : ((1019958483963/10000000000000 : ℚ) : ℝ) ≤ stT301 93 := by
  have hc : ((983613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1019958483963/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((983613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c94 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-124337/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1899097/2500000) (δ := 15159/1000000000) (ψ := 1041953/1000000) 301 217
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t94 : ((-128256809989/1250000000000 : ℚ) : ℝ) ≤ stT301 94 := by
  have hc : ((-248699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128256809989/1250000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-248699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c95 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((199647/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29709/2000000) (δ := 15167/1000000000) (ψ := 1041953/1000000) 301 218
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t95 : ((102406455103/1000000000000 : ℚ) : ℝ) ≤ stT301 95 := by
  have hc : ((199627/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102406455103/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((199627/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c96 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-124849/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1932777/2500000) (δ := 15067/1000000000) (ψ := 1041953/1000000) 301 218
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t96 : ((-254872537983/2500000000000 : ℚ) : ℝ) ≤ stT301 96 := by
  have hc : ((-249723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254872537983/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-249723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c97 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((498721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5589/312500) (δ := 7587/500000000) (ψ := 1041953/1000000) 301 219
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t97 : ((253161802583/2500000000000 : ℚ) : ℝ) ≤ stT301 97 := by
  have hc : ((498671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253161802583/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((498671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c98 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-496041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 235599/312500) (δ := 7537/500000000) (ψ := 1041953/1000000) 301 219
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t98 : ((-501127811923/5000000000000 : ℚ) : ℝ) ≤ stT301 98 := by
  have hc : ((-496091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501127811923/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-496091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c99 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((977687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264557/5000000) (δ := 15181/1000000000) (ψ := 1041953/1000000) 301 220
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t99 : ((982511105719/10000000000000 : ℚ) : ℝ) ≤ stT301 99 := by
  have hc : ((977587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((982511105719/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((977587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c100 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-946657/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879217/1250000) (δ := 7611/500000000) (ψ := 1041953/1000000) 301 220
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t100 : ((-946757/10000000 : ℚ) : ℝ) ≤ stT301 100 := by
  have hc : ((-946757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-946757/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-946757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c101 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((444733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1186551/10000000) (δ := 3023/200000000) (ψ := 1041953/1000000) 301 221
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t101 : ((442476038271/5000000000000 : ℚ) : ℝ) ≤ stT301 101 := by
  have hc : ((444683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442476038271/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((444683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c102 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-397839/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1245461/2000000) (δ := 943/62500000) (ψ := 1041953/1000000) 301 221
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t102 : ((-98492249393/1250000000000 : ℚ) : ℝ) ≤ stT301 102 := by
  have hc : ((-397889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98492249393/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-397889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c103 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((655707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2139193/10000000) (δ := 3019/200000000) (ψ := 1041953/1000000) 301 222
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t103 : ((645988589703/10000000000000 : ℚ) : ℝ) ≤ stT301 103 := by
  have hc : ((655607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((645988589703/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((655607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c104 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-231669/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5131387/10000000) (δ := 3039/200000000) (ψ := 1041953/1000000) 301 222
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t104 : ((-227219248739/5000000000000 : ℚ) : ℝ) ≤ stT301 104 := by
  have hc : ((-231719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227219248739/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-231719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c105 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((218801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421941/1250000) (δ := 151/10000000) (ψ := 1041953/1000000) 301 223
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t105 : ((2134303059/100000000000 : ℚ) : ℝ) ≤ stT301 105 := by
  have hc : ((218701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2134303059/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((218701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c106 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((67867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1878597/5000000) (δ := 15103/1000000000) (ψ := 1041953/1000000) 301 223
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t106 : ((13164214119/2000000000000 : ℚ) : ℝ) ≤ stT301 106 := by
  have hc : ((67767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13164214119/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((67767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c107 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-373873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -976989/2000000) (δ := 15093/1000000000) (ψ := 1041953/1000000) 301 224
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t107 : ((-361533536101/10000000000000 : ℚ) : ℝ) ≤ stT301 107 := by
  have hc : ((-373973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361533536101/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-373973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c108 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((13259/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2115111/10000000) (δ := 15093/1000000000) (ψ := 1041953/1000000) 301 224
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t108 : ((51026193/800000000 : ℚ) : ℝ) ≤ stT301 108 := by
  have hc : ((13257/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51026193/800000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((13257/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c109 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-443809/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6657361/10000000) (δ := 7593/500000000) (ψ := 1041953/1000000) 301 225
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t109 : ((-425140134393/5000000000000 : ℚ) : ℝ) ≤ stT301 109 := by
  have hc : ((-443859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425140134393/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-443859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c110 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((99631/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107423/5000000) (δ := 15217/1000000000) (ψ := 1041953/1000000) 301 225
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t110 : ((47492418951/500000000000 : ℚ) : ℝ) ≤ stT301 110 := by
  have hc : ((99621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47492418951/500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((99621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c111 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-945511/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1404979/2000000) (δ := 7593/500000000) (ψ := 1041953/1000000) 301 225
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t111 : ((-448767122769/5000000000000 : ℚ) : ℝ) ≤ stT301 111 := by
  have hc : ((-945611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448767122769/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-945611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c112 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((143069/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -483549/2500000) (δ := 1903/125000000) (ψ := 1041953/1000000) 301 226
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t112 : ((135168573639/2000000000000 : ℚ) : ℝ) ≤ stT301 112 := by
  have hc : ((143049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135168573639/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((143049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c113 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-325097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594347/1250000) (δ := 15079/1000000000) (ψ := 1041953/1000000) 301 226
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t113 : ((-305919647037/10000000000000 : ℚ) : ℝ) ≤ stT301 113 := by
  have hc : ((-325197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305919647037/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-325197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c114 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-6313/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4323211/10000000) (δ := 3793/250000000) (ψ := 1041953/1000000) 301 227
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t114 : ((-2958206881/200000000000 : ℚ) : ℝ) ≤ stT301 114 := by
  have hc : ((-6317/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2958206881/200000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-6317/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c115 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((124391/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2248899/10000000) (δ := 15231/1000000000) (ψ := 1041953/1000000) 301 227
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t115 : ((14497056873/250000000000 : ℚ) : ℝ) ≤ stT301 115 := by
  have hc : ((124371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14497056873/250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((124371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c116 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-934471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86799/125000) (δ := 3033/200000000) (ψ := 1041953/1000000) 301 228
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t116 : ((-867727678367/10000000000000 : ℚ) : ℝ) ≤ stT301 116 := by
  have hc : ((-934571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-867727678367/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-934571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c117 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((981271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48461/1000000) (δ := 7569/500000000) (ψ := 1041953/1000000) 301 228
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t117 : ((1814185179/20000000000 : ℚ) : ℝ) ≤ stT301 117 := by
  have hc : ((981171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1814185179/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((981171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c118 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-715319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1479923/2500000) (δ := 7619/500000000) (ψ := 1041953/1000000) 301 228
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t118 : ((-26343873837/400000000000 : ℚ) : ℝ) ≤ stT301 118 := by
  have hc : ((-715419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26343873837/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-715419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c119 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((97161/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137523/400000) (δ := 15157/1000000000) (ψ := 1041953/1000000) 301 229
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t119 : ((44510729739/2500000000000 : ℚ) : ℝ) ≤ stT301 119 := by
  have hc : ((97111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44510729739/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((97111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c120 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((82859/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2859071/10000000) (δ := 15057/1000000000) (ψ := 1041953/1000000) 301 229
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t120 : ((7562123793/200000000000 : ℚ) : ℝ) ≤ stT301 120 := by
  have hc : ((82839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7562123793/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((82839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c121 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-175519/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1320809/2000000) (δ := 15153/1000000000) (ψ := 1041953/1000000) 301 230
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t121 : ((-159580925049/2000000000000 : ℚ) : ℝ) ≤ stT301 121 := by
  have hc : ((-175539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159580925049/2000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-175539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c122 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((986543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -205297/5000000) (δ := 15053/1000000000) (ψ := 1041953/1000000) 301 230
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t122 : ((893083075151/10000000000000 : ℚ) : ℝ) ≤ stT301 122 := by
  have hc : ((986443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((893083075151/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((986443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c123 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-41311/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5732289/10000000) (δ := 303/20000000) (ψ := 1041953/1000000) 301 230
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t123 : ((-14901809923/250000000000 : ℚ) : ℝ) ≤ stT301 123 := by
  have hc : ((-165269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14901809923/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-165269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c124 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((17783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3882531/10000000) (δ := 753/50000000) (ψ := 1041953/1000000) 301 231
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t124 : ((7939896879/5000000000000 : ℚ) : ℝ) ≤ stT301 124 := by
  have hc : ((17683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7939896879/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((17683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c125 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((162221/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2161699/10000000) (δ := 15243/1000000000) (ψ := 1041953/1000000) 301 231
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t125 : ((36268120423/625000000000 : ℚ) : ℝ) ≤ stT301 125 := by
  have hc : ((40549/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36268120423/625000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((40549/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c126 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-496313/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7550193/10000000) (δ := 15167/1000000000) (ψ := 1041953/1000000) 301 232
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t126 : ((-442195402173/5000000000000 : ℚ) : ℝ) ≤ stT301 126 := by
  have hc : ((-496363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-442195402173/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-496363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c127 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((50107/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -800803/5000000) (δ := 3809/250000000) (ψ := 1041953/1000000) 301 232
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t127 : ((44457201117/625000000000 : ℚ) : ℝ) ≤ stT301 127 := by
  have hc : ((200403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44457201117/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((200403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c128 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-14881/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2150201/5000000) (δ := 3809/250000000) (ψ := 1041953/1000000) 301 232
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t128 : ((-3290479161/250000000000 : ℚ) : ℝ) ≤ stT301 128 := by
  have hc : ((-14891/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3290479161/250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-14891/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c129 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-75627/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1110291/2000000) (δ := 7587/500000000) (ψ := 1041953/1000000) 301 233
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t129 : ((-133193746829/2500000000000 : ℚ) : ℝ) ≤ stT301 129 := by
  have hc : ((-151279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133193746829/2500000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-151279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c130 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((15541/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5187/200000) (δ := 7587/500000000) (ψ := 1041953/1000000) 301 233
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t130 : ((109031903799/1250000000000 : ℚ) : ℝ) ≤ stT301 130 := by
  have hc : ((248631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109031903799/1250000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((248631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c131 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-372147/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3012841/5000000) (δ := 7537/500000000) (ψ := 1041953/1000000) 301 233
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t131 : ((-65038075977/1000000000000 : ℚ) : ℝ) ≤ stT301 131 := by
  have hc : ((-372197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65038075977/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-372197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c132 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-13131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197991/500000) (δ := 15121/1000000000) (ψ := 1041953/1000000) 301 234
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t132 : ((-11516116859/10000000000000 : ℚ) : ℝ) ≤ stT301 132 := by
  have hc : ((-13231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11516116859/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-13231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c133 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((386329/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214931/1250000) (δ := 15121/1000000000) (ψ := 1041953/1000000) 301 234
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t133 : ((334945997411/5000000000000 : ℚ) : ℝ) ≤ stT301 133 := by
  have hc : ((386279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334945997411/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((386279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c134 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-980239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3678081/5000000) (δ := 30221/1000000000) (ψ := 1041953/1000000) 301 234
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t134 : ((-846884471591/10000000000000 : ℚ) : ℝ) ≤ stT301 134 := by
  have hc : ((-980339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-846884471591/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-980339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c135 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((451099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2757001/10000000) (δ := 15089/1000000000) (ψ := 1041953/1000000) 301 235
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t135 : ((194078850669/5000000000000 : ℚ) : ℝ) ≤ stT301 135 := by
  have hc : ((450999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194078850669/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((450999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c136 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((218467/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699131/2500000) (δ := 7557/500000000) (ψ := 1041953/1000000) 301 235
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t136 : ((46822707541/1250000000000 : ℚ) : ℝ) ≤ stT301 136 := by
  have hc : ((218417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46822707541/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((218417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c137 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-245863/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7398549/10000000) (δ := 15107/1000000000) (ψ := 1041953/1000000) 301 236
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t137 : ((-820610859/9765625000 : ℚ) : ℝ) ≤ stT301 137 := by
  have hc : ((-15368/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820610859/9765625000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-15368/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c138 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((179419/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962921/5000000) (δ := 1887/125000000) (ψ := 1041953/1000000) 301 236
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t138 : ((9544388679/156250000000 : ℚ) : ℝ) ≤ stT301 138 := by
  have hc : ((89697/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9544388679/156250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((89697/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c139 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((41759/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1753717/5000000) (δ := 3799/250000000) (ψ := 1041953/1000000) 301 236
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t139 : ((4424784749/312500000000 : ℚ) : ℝ) ≤ stT301 139 := by
  have hc : ((20867/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4424784749/312500000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((20867/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c140 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-57091/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6806233/10000000) (δ := 15203/1000000000) (ψ := 1041953/1000000) 301 237
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t140 : ((-38604821059/500000000000 : ℚ) : ℝ) ≤ stT301 140 := by
  have hc : ((-228389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38604821059/500000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-228389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c141 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((836377/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145039/1000000) (δ := 151/10000000) (ψ := 1041953/1000000) 301 237
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t141 : ((704271511827/10000000000000 : ℚ) : ℝ) ≤ stT301 141 := by
  have hc : ((836277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((704271511827/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((836277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c142 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((23723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1933839/5000000) (δ := 151/10000000) (ψ := 1041953/1000000) 301 237
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t142 : ((19823972763/10000000000000 : ℚ) : ℝ) ≤ stT301 142 := by
  have hc : ((23623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19823972763/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((23623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c143 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-434461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6559541/10000000) (δ := 1511/100000000) (ψ := 1041953/1000000) 301 238
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t143 : ((-363356782173/5000000000000 : ℚ) : ℝ) ≤ stT301 143 := by
  have hc : ((-434511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363356782173/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-434511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c144 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((54043/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131567/1000000) (δ := 15193/1000000000) (ψ := 1041953/1000000) 301 238
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t144 : ((180122427951/2500000000000 : ℚ) : ℝ) ≤ stT301 144 := by
  have hc : ((216147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180122427951/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((216147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c145 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((13993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3892007/10000000) (δ := 1521/100000000) (ψ := 1041953/1000000) 301 238
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t145 : ((5768748711/5000000000000 : ℚ) : ℝ) ≤ stT301 145 := by
  have hc : ((13893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5768748711/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((13893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c146 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-885163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6644099/10000000) (δ := 15217/1000000000) (ψ := 1041953/1000000) 301 239
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t146 : ((-366324485189/5000000000000 : ℚ) : ℝ) ≤ stT301 146 := by
  have hc : ((-885263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366324485189/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-885263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c147 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((823613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150761/1000000) (δ := 7593/500000000) (ψ := 1041953/1000000) 301 239
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t147 : ((339610996609/5000000000000 : ℚ) : ℝ) ≤ stT301 147 := by
  have hc : ((823513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339610996609/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((823513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c148 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((132757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 718823/2000000) (δ := 15217/1000000000) (ψ := 1041953/1000000) 301 239
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t148 : ((54521629029/5000000000000 : ℚ) : ℝ) ≤ stT301 148 := by
  have hc : ((132657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54521629029/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((132657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c149 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-474141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3523219/5000000) (δ := 609/40000000) (ψ := 1041953/1000000) 301 240
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t149 : ((-12139763791/156250000000 : ℚ) : ℝ) ≤ stT301 149 := by
  have hc : ((-474191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12139763791/156250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-474191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c150 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((138591/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2013041/10000000) (δ := 121/8000000) (ψ := 1041953/1000000) 301 240
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t150 : ((7071416701/125000000000 : ℚ) : ℝ) ≤ stT301 150 := by
  have hc : ((138571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7071416701/125000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((138571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c151 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((45899/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149351/500000) (δ := 7589/500000000) (ψ := 1041953/1000000) 301 240
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t151 : ((18670941531/625000000000 : ℚ) : ℝ) ≤ stT301 151 := by
  have hc : ((91773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18670941531/625000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((91773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c152 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-999199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1938479/2500000) (δ := 3783/250000000) (ψ := 1041953/1000000) 301 241
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t152 : ((-202634853323/2500000000000 : ℚ) : ℝ) ≤ stT301 152 := by
  have hc : ((-999299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202634853323/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-999299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c153 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((214329/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2819473/10000000) (δ := 15171/1000000000) (ψ := 1041953/1000000) 301 241
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t153 : ((43308571527/1250000000000 : ℚ) : ℝ) ≤ stT301 153 := by
  have hc : ((214279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43308571527/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((214279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c154 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((672559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2082839/10000000) (δ := 15071/1000000000) (ψ := 1041953/1000000) 301 241
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t154 : ((270941128149/5000000000000 : ℚ) : ℝ) ≤ stT301 154 := by
  have hc : ((672459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270941128149/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((672459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c155 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-467907/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1390679/2000000) (δ := 15171/1000000000) (ψ := 1041953/1000000) 301 241
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t155 : ((-18793621077/250000000000 : ℚ) : ℝ) ≤ stT301 155 := by
  have hc : ((-467957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18793621077/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-467957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c156 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((467/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -978829/2500000) (δ := 3791/250000000) (ψ := 1041953/1000000) 301 242
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t156 : ((571707/1562500000 : ℚ) : ℝ) ≤ stT301 156 := by
  have hc : ((457/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571707/1562500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((457/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c157 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((468439/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 893009/10000000) (δ := 15139/1000000000) (ψ := 1041953/1000000) 301 242
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t157 : ((186907351727/2500000000000 : ℚ) : ℝ) ≤ stT301 157 := by
  have hc : ((468389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186907351727/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((468389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c158 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-160579/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2835391/5000000) (δ := 15139/1000000000) (ψ := 1041953/1000000) 301 242
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t158 : ((-15971224629/312500000000 : ℚ) : ℝ) ≤ stT301 158 := by
  have hc : ((-40151/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15971224629/312500000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-40151/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c159 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-64803/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1322377/2500000) (δ := 7623/500000000) (ψ := 1041953/1000000) 301 243
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t159 : ((-25701030953/625000000000 : ℚ) : ℝ) ≤ stT301 159 := by
  have hc : ((-129631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25701030953/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-129631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c160 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((243493/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -285817/5000000) (δ := 7623/500000000) (ψ := 1041953/1000000) 301 243
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t160 : ((48119563323/625000000000 : ℚ) : ℝ) ≤ stT301 160 := by
  have hc : ((60867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48119563323/625000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((60867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c161 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-37929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4116817/10000000) (δ := 7573/500000000) (ψ := 1041953/1000000) 301 243
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t161 : ((-29931667669/5000000000000 : ℚ) : ℝ) ≤ stT301 161 := by
  have hc : ((-37979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29931667669/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-37979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c162 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-186543/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6931667/10000000) (δ := 61/4000000) (ψ := 1041953/1000000) 301 244
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t162 : ((-5863115401/80000000000 : ℚ) : ℝ) ≤ stT301 162 := by
  have hc : ((-186563/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5863115401/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-186563/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c163 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((605547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2300857/10000000) (δ := 303/20000000) (ψ := 1041953/1000000) 301 244
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t163 : ((23711120861/500000000000 : ℚ) : ℝ) ≤ stT301 163 := by
  have hc : ((605447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23711120861/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((605447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c164 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((151329/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143849/625000) (δ := 15153/1000000000) (ψ := 1041953/1000000) 301 244
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t164 : ((3692139121/78125000000 : ℚ) : ℝ) ≤ stT301 164 := by
  have hc : ((18913/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3692139121/78125000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((18913/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c165 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-46223/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6876031/10000000) (δ := 303/20000000) (ψ := 1041953/1000000) 301 244
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t165 : ((-8997112943/125000000000 : ℚ) : ℝ) ≤ stT301 165 := by
  have hc : ((-11557/12500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8997112943/125000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-11557/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c166 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-28551/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4285101/10000000) (δ := 379/25000000) (ψ := 1041953/1000000) 301 245
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t166 : ((-22175410221/2000000000000 : ℚ) : ℝ) ≤ stT301 166 := by
  have hc : ((-28571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22175410221/2000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-28571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c167 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((248901/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 234489/10000000) (δ := 753/50000000) (ψ := 1041953/1000000) 301 245
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t167 : ((48146493237/625000000000 : ℚ) : ℝ) ≤ stT301 167 := by
  have hc : ((62219/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48146493237/625000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((62219/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c168 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-157283/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4726989/10000000) (δ := 15143/1000000000) (ψ := 1041953/1000000) 301 245
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t168 : ((-121385084161/5000000000000 : ℚ) : ℝ) ≤ stT301 168 := by
  have hc : ((-157333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121385084161/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-157333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c169 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-429987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6515037/10000000) (δ := 3767/250000000) (ψ := 1041953/1000000) 301 246
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t169 : ((-330797791547/5000000000000 : ℚ) : ℝ) ≤ stT301 169 := by
  have hc : ((-430037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330797791547/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-430037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c170 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((168681/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2075513/10000000) (δ := 3027/200000000) (ψ := 1041953/1000000) 301 246
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t170 : ((2021141881/39062500000 : ℚ) : ℝ) ≤ stT301 170 := by
  have hc : ((10541/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2021141881/39062500000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((10541/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c171 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((296833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93519/400000) (δ := 3767/250000000) (ψ := 1041953/1000000) 301 246
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t171 : ((226955598977/5000000000000 : ℚ) : ℝ) ≤ stT301 171 := by
  have hc : ((296783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226955598977/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((296783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c172 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-22497/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6725727/10000000) (δ := 3027/200000000) (ψ := 1041953/1000000) 301 246
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t172 : ((-34311422507/500000000000 : ℚ) : ℝ) ≤ stT301 172 := by
  have hc : ((-44999/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34311422507/500000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-44999/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c173 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-68409/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2309959/5000000) (δ := 607/40000000) (ψ := 1041953/1000000) 301 247
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t173 : ((-13007353031/625000000000 : ℚ) : ℝ) ≤ stT301 173 := by
  have hc : ((-34217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13007353031/625000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-34217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c174 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((248403/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141367/5000000) (δ := 603/40000000) (ψ := 1041953/1000000) 301 247
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t174 : ((47073716261/625000000000 : ℚ) : ℝ) ≤ stT301 174 := by
  have hc : ((124189/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47073716261/625000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((124189/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c175 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-41039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2014809/5000000) (δ := 607/40000000) (ψ := 1041953/1000000) 301 247
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t175 : ((-31098163131/10000000000000 : ℚ) : ℝ) ≤ stT301 175 := by
  have hc : ((-41139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31098163131/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-41139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c176 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-982871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7390601/10000000) (δ := 15221/1000000000) (ψ := 1041953/1000000) 301 248
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t176 : ((-740942897409/10000000000000 : ℚ) : ℝ) ≤ stT301 176 := by
  have hc : ((-982971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-740942897409/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-982971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c177 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((31453/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563543/5000000) (δ := 7541/500000000) (ψ := 1041953/1000000) 301 248
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t177 : ((11817002589/500000000000 : ℚ) : ℝ) ≤ stT301 177 := by
  have hc : ((31443/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11817002589/500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((31443/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c178 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((902637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278087/2500000) (δ := 15221/1000000000) (ψ := 1041953/1000000) 301 248
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t178 : ((676479460147/10000000000000 : ℚ) : ℝ) ≤ stT301 178 := by
  have hc : ((902537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((676479460147/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((902537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c179 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-106311/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5328079/10000000) (δ := 15121/1000000000) (ψ := 1041953/1000000) 301 248
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t179 : ((-19868904329/500000000000 : ℚ) : ℝ) ≤ stT301 179 := by
  have hc : ((-106331/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19868904329/500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-106331/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c180 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-12281/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6187707/10000000) (δ := 7607/500000000) (ψ := 1041953/1000000) 301 249
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t180 : ((-36619526619/625000000000 : ℚ) : ℝ) ≤ stT301 180 := by
  have hc : ((-196521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36619526619/625000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-196521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c181 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((17283/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1009353/5000000) (δ := 15089/1000000000) (ψ := 1041953/1000000) 301 249
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t181 : ((12844491967/250000000000 : ℚ) : ℝ) ≤ stT301 181 := by
  have hc : ((34561/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12844491967/250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((34561/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c182 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((659301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 531817/2500000) (δ := 15089/1000000000) (ψ := 1041953/1000000) 301 249
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t182 : ((488632082049/10000000000000 : ℚ) : ℝ) ≤ stT301 182 := by
  have hc : ((659201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488632082049/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((659201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c183 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-160257/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195331/312500) (δ := 15189/1000000000) (ψ := 1041953/1000000) 301 249
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t183 : ((-59240142247/1000000000000 : ℚ) : ℝ) ≤ stT301 183 := by
  have hc : ((-160277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59240142247/1000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-160277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c184 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-270583/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1339137/2500000) (δ := 15207/1000000000) (ψ := 1041953/1000000) 301 250
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t184 : ((-19951335393/500000000000 : ℚ) : ℝ) ≤ stT301 184 := by
  have hc : ((-270633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19951335393/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-270633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c185 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((872173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -638961/5000000) (δ := 3799/250000000) (ψ := 1041953/1000000) 301 250
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t185 : ((320580139311/5000000000000 : ℚ) : ℝ) ≤ stT301 185 := by
  have hc : ((872073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320580139311/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((872073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c186 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((55419/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555731/2000000) (δ := 3799/250000000) (ψ := 1041953/1000000) 301 250
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t186 : ((16250394011/500000000000 : ℚ) : ℝ) ≤ stT301 186 := by
  have hc : ((110813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16250394011/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((110813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c187 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-182929/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170339/250000) (δ := 3799/250000000) (ψ := 1041953/1000000) 301 250
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t187 : ((-133785664077/2000000000000 : ℚ) : ℝ) ≤ stT301 187 := by
  have hc : ((-182949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133785664077/2000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-182949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c188 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-74489/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -976219/2000000) (δ := 3801/250000000) (ψ := 1041953/1000000) 301 251
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t188 : ((-2173651057/80000000000 : ℚ) : ℝ) ≤ stT301 188 := by
  have hc : ((-74509/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2173651057/80000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-74509/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c189 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((937437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55563/625000) (δ := 15199/1000000000) (ψ := 1041953/1000000) 301 251
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t189 : ((21306607347/312500000000 : ℚ) : ℝ) ≤ stT301 189 := by
  have hc : ((937337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21306607347/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((937337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c190 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((165811/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 616387/2000000) (δ := 59/3906250) (ψ := 1041953/1000000) 301 251
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t190 : ((30063906809/1250000000000 : ℚ) : ℝ) ≤ stT301 190 := by
  have hc : ((165761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30063906809/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((165761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c191 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-946447/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1758027/2500000) (δ := 15199/1000000000) (ψ := 1041953/1000000) 301 251
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t191 : ((-27395909821/400000000000 : ℚ) : ℝ) ≤ stT301 191 := by
  have hc : ((-946547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27395909821/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-946547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c192 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-321917/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37971/80000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 252
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t192 : ((-29049475587/1250000000000 : ℚ) : ℝ) ≤ stT301 192 := by
  have hc : ((-322017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29049475587/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-322017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c193 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((472219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104661/1250000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 252
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t193 : ((67974865747/1000000000000 : ℚ) : ℝ) ≤ stT301 193 := by
  have hc : ((472169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67974865747/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((472169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c194 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((343033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190727/625000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 252
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t194 : ((123105745407/5000000000000 : ℚ) : ℝ) ≤ stT301 194 := by
  have hc : ((342933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123105745407/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((342933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c195 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-9311/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1384107/2000000) (δ := 1899/125000000) (ψ := 1041953/1000000) 301 252
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t195 : ((-41677893/625000000 : ℚ) : ℝ) ≤ stT301 195 := by
  have hc : ((-582/625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41677893/625000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-582/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c196 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-196793/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -987663/2000000) (δ := 7559/500000000) (ψ := 1041953/1000000) 301 253
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t196 : ((-70301099549/2500000000000 : ℚ) : ℝ) ≤ stT301 196 := by
  have hc : ((-196843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70301099549/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-196843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c197 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((225813/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108767/10000000) (δ := 7609/500000000) (ψ := 1041953/1000000) 301 253
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t197 : ((4021679409/62500000000 : ℚ) : ℝ) ≤ stT301 197 := by
  have hc : ((56447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4021679409/62500000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((56447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c198 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((235423/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1350683/5000000) (δ := 7559/500000000) (ψ := 1041953/1000000) 301 253
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t198 : ((167272294537/5000000000000 : ℚ) : ℝ) ≤ stT301 198 := by
  have hc : ((235373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167272294537/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((235373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c199 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-855299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 649231/1000000) (δ := 3037/200000000) (ψ := 1041953/1000000) 301 253
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t199 : ((-303188476959/5000000000000 : ℚ) : ℝ) ≤ stT301 199 := by
  have hc : ((-855399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303188476959/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-855399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c200 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-285081/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5443747/10000000) (δ := 7589/500000000) (ψ := 1041953/1000000) 301 254
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t200 : ((-201618126017/5000000000000 : ℚ) : ℝ) ≤ stT301 200 := by
  have hc : ((-285131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201618126017/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-285131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c201 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((779937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -845289/5000000) (δ := 7589/500000000) (ψ := 1041953/1000000) 301 254
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t201 : ((110010825753/2000000000000 : ℚ) : ℝ) ≤ stT301 201 := by
  have hc : ((779837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110010825753/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((779837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c202 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((684017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021927/5000000) (δ := 7539/500000000) (ψ := 1041953/1000000) 301 254
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t202 : ((481201949449/10000000000000 : ℚ) : ℝ) ≤ stT301 202 := by
  have hc : ((683917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((481201949449/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((683917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c203 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-669231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230397/400000) (δ := 121/8000000) (ψ := 1041953/1000000) 301 254
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t203 : ((-469778663653/10000000000000 : ℚ) : ℝ) ≤ stT301 203 := by
  have hc : ((-669331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469778663653/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-669331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c204 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-200301/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6250253/10000000) (δ := 119/7812500) (ψ := 1041953/1000000) 301 255
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t204 : ((-70128222983/1250000000000 : ℚ) : ℝ) ≤ stT301 204 := by
  have hc : ((-100163/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70128222983/1250000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-100163/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c205 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((8068/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80329/312500) (δ := 119/7812500) (ψ := 1041953/1000000) 301 255
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t205 : ((9014147109/250000000000 : ℚ) : ℝ) ≤ stT301 205 := by
  have hc : ((129063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9014147109/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((129063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c206 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((906231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1091287/10000000) (δ := 15071/1000000000) (ψ := 1041953/1000000) 301 255
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t206 : ((631331370023/10000000000000 : ℚ) : ℝ) ≤ stT301 206 := by
  have hc : ((906131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((631331370023/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((906131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c207 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-39717/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295959/625000) (δ := 119/7812500) (ψ := 1041953/1000000) 301 255
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t207 : ((-55227898491/2500000000000 : ℚ) : ℝ) ≤ stT301 207 := by
  have hc : ((-79459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55227898491/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-79459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c208 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-195887/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -459131/625000) (δ := 15239/1000000000) (ψ := 1041953/1000000) 301 256
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t208 : ((-1061228219/15625000000 : ℚ) : ℝ) ≤ stT301 208 := by
  have hc : ((-195907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1061228219/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-195907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c209 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((75941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -934239/2500000) (δ := 1883/125000000) (ψ := 1041953/1000000) 301 256
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t209 : ((26230140737/5000000000000 : ℚ) : ℝ) ≤ stT301 209 := by
  have hc : ((75841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26230140737/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((75841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c210 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((998317/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18131/1250000) (δ := 3791/250000000) (ψ := 1041953/1000000) 301 256
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t210 : ((137766922821/2000000000000 : ℚ) : ℝ) ≤ stT301 210 := by
  have hc : ((998217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137766922821/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((998217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c211 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((24697/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3429779/10000000) (δ := 15139/1000000000) (ψ := 1041953/1000000) 301 256
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t211 : ((8496750483/625000000000 : ℚ) : ℝ) ≤ stT301 211 := by
  have hc : ((49369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8496750483/625000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((49369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c212 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-940559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3493837/5000000) (δ := 1883/125000000) (ψ := 1041953/1000000) 301 256
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t212 : ((-646047423177/10000000000000 : ℚ) : ℝ) ≤ stT301 212 := by
  have hc : ((-940659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-646047423177/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-940659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c213 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-96033/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5179099/10000000) (δ := 15247/1000000000) (ψ := 1041953/1000000) 301 257
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t213 : ((-65814459017/2000000000000 : ℚ) : ℝ) ≤ stT301 213 := by
  have hc : ((-96053/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65814459017/2000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-96053/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c214 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((24653/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330893/2000000) (δ := 3789/250000000) (ψ := 1041953/1000000) 301 257
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t214 : ((26960455683/500000000000 : ℚ) : ℝ) ≤ stT301 214 := by
  have hc : ((197199/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26960455683/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((197199/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c215 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((737473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185369/1000000) (δ := 3789/250000000) (ψ := 1041953/1000000) 301 257
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t215 : ((251441980881/5000000000000 : ℚ) : ℝ) ≤ stT301 215 := by
  have hc : ((737373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251441980881/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((737373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c216 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-21499/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5345591/10000000) (δ := 3789/250000000) (ψ := 1041953/1000000) 301 257
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t216 : ((-7315471121/200000000000 : ℚ) : ℝ) ≤ stT301 216 := by
  have hc : ((-21503/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7315471121/200000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-21503/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c217 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-926071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137733/200000) (δ := 15149/1000000000) (ψ := 1041953/1000000) 301 258
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t217 : ((-125745310499/2000000000000 : ℚ) : ℝ) ≤ stT301 217 := by
  have hc : ((-926171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125745310499/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-926171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c218 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((24839/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3426881/10000000) (δ := 15249/1000000000) (ψ := 1041953/1000000) 301 258
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t218 : ((6725846421/500000000000 : ℚ) : ℝ) ≤ stT301 218 := by
  have hc : ((49653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6725846421/500000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((49653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c219 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((999977/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8543/5000000) (δ := 15149/1000000000) (ψ := 1041953/1000000) 301 258
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t219 : ((675653884349/10000000000000 : ℚ) : ℝ) ≤ stT301 219 := by
  have hc : ((999877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((675653884349/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((999877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c220 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((47869/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1722663/5000000) (δ := 7577/500000000) (ψ := 1041953/1000000) 301 258
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t220 : ((8064094239/625000000000 : ℚ) : ℝ) ≤ stT301 220 := by
  have hc : ((11961/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8064094239/625000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((11961/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c221 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-28803/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428629/625000) (δ := 7577/500000000) (ψ := 1041953/1000000) 301 258
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t221 : ((-155016820177/2500000000000 : ℚ) : ℝ) ≤ stT301 221 := by
  have hc : ((-230449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155016820177/2500000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-230449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c222 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-17909/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5452663/10000000) (δ := 15061/1000000000) (ψ := 1041953/1000000) 301 259
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t222 : ((-96174784629/2500000000000 : ℚ) : ℝ) ≤ stT301 222 := by
  have hc : ((-143297/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96174784629/2500000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-143297/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c223 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((338083/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2070627/10000000) (δ := 15061/1000000000) (ψ := 1041953/1000000) 301 259
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t223 : ((226363460417/5000000000000 : ℚ) : ℝ) ≤ stT301 223 := by
  have hc : ((338033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226363460417/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((338033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c224 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((868557/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324071/2500000) (δ := 15161/1000000000) (ψ := 1041953/1000000) 301 259
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t224 : ((580262149921/10000000000000 : ℚ) : ℝ) ≤ stT301 224 := by
  have hc : ((868457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((580262149921/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((868457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c225 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-284507/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232411/500000) (δ := 15161/1000000000) (ψ := 1041953/1000000) 301 259
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t225 : ((-189738094869/10000000000000 : ℚ) : ℝ) ≤ stT301 225 := by
  have hc : ((-284607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189738094869/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-284607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c226 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-499311/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544549/2000000) (δ := 6047/200000000) (ψ := 1041953/1000000) 301 260
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t226 : ((-332170442951/5000000000000 : ℚ) : ℝ) ≤ stT301 226 := by
  have hc : ((-499361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332170442951/5000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-499361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c227 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-94121/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220021/500000) (δ := 3047/200000000) (ψ := 1041953/1000000) 301 260
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t227 : ((-15625888201/1250000000000 : ℚ) : ℝ) ≤ stT301 227 := by
  have hc : ((-94171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15625888201/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-94171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c228 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((452993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092731/10000000) (δ := 3047/200000000) (ψ := 1041953/1000000) 301 260
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t228 : ((149984374419/2500000000000 : ℚ) : ℝ) ≤ stT301 228 := by
  have hc : ((452943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149984374419/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((452943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c229 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((318497/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220051/1000000) (δ := 3047/200000000) (ψ := 1041953/1000000) 301 260
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t229 : ((105217754823/2500000000000 : ℚ) : ℝ) ≤ stT301 229 := by
  have hc : ((318447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105217754823/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((318447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c230 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-145453/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5479379/10000000) (δ := 237/15625000) (ψ := 1041953/1000000) 301 260
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t230 : ((-47962714559/1250000000000 : ℚ) : ℝ) ≤ stT301 230 := by
  have hc : ((-72739/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47962714559/1250000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-72739/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c231 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-234323/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6963939/10000000) (δ := 3807/250000000) (ψ := 1041953/1000000) 301 261
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t231 : ((-1204607307/19531250000 : ℚ) : ℝ) ≤ stT301 231 := by
  have hc : ((-58587/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1204607307/19531250000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-58587/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c232 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((21329/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23209/62500) (δ := 3807/250000000) (ψ := 1041953/1000000) 301 261
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t232 : ((437086179/78125000000 : ℚ) : ℝ) ≤ stT301 232 := by
  have hc : ((2663/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437086179/78125000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((2663/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c233 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((981863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238431/5000000) (δ := 1891/125000000) (ψ := 1041953/1000000) 301 261
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t233 : ((643173558323/10000000000000 : ℚ) : ℝ) ≤ stT301 233 := by
  have hc : ((981763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((643173558323/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((981763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c234 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((113767/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274587/1000000) (δ := 603/40000000) (ψ := 1041953/1000000) 301 261
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t234 : ((929442753/31250000000 : ℚ) : ℝ) ≤ stT301 234 := by
  have hc : ((56871/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((929442753/31250000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((56871/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c235 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-72507/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5954831/10000000) (δ := 603/40000000) (ψ := 1041953/1000000) 301 261
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t235 : ((-47304942093/1000000000000 : ℚ) : ℝ) ≤ stT301 235 := by
  have hc : ((-72517/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47304942093/1000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-72517/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c236 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-34743/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204931/312500) (δ := 761/50000000) (ψ := 1041953/1000000) 301 262
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t236 : ((-4523677183/80000000000 : ℚ) : ℝ) ≤ stT301 236 := by
  have hc : ((-34747/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4523677183/80000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-34747/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c237 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((109309/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -843999/2500000) (δ := 189/12500000) (ψ := 1041953/1000000) 301 262
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t237 : ((70971259371/5000000000000 : ℚ) : ℝ) ≤ stT301 237 := by
  have hc : ((109259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70971259371/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((109259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c238 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((498277/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41519/2000000) (δ := 761/50000000) (ψ := 1041953/1000000) 301 262
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t238 : ((322952236081/5000000000000 : ℚ) : ℝ) ≤ stT301 238 := by
  have hc : ((498227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322952236081/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((498227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c239 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((190913/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2947563/10000000) (δ := 15183/1000000000) (ψ := 1041953/1000000) 301 262
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t239 : ((61729484049/2500000000000 : ℚ) : ℝ) ≤ stT301 239 := by
  have hc : ((190863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61729484049/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((190863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c240 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-761111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6089551/10000000) (δ := 189/12500000) (ψ := 1041953/1000000) 301 262
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t240 : ((-245680089039/5000000000000 : ℚ) : ℝ) ≤ stT301 240 := by
  have hc : ((-761211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245680089039/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-761211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c241 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-2671/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6489517/10000000) (δ := 1509/100000000) (ψ := 1041953/1000000) 301 263
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t241 : ((-27531914337/500000000000 : ℚ) : ℝ) ≤ stT301 241 := by
  have hc : ((-42741/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27531914337/500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-42741/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c242 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((219567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -674713/2000000) (δ := 1509/100000000) (ψ := 1041953/1000000) 301 263
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t242 : ((17634831851/1250000000000 : ℚ) : ℝ) ≤ stT301 242 := by
  have hc : ((219467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17634831851/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((219467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c243 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((994153/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270481/10000000) (δ := 15113/1000000000) (ψ := 1041953/1000000) 301 263
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t243 : ((1275369999/20000000000 : ℚ) : ℝ) ≤ stT301 243 := by
  have hc : ((994053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1275369999/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((994053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c244 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((428509/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1409943/5000000) (δ := 15113/1000000000) (ψ := 1041953/1000000) 301 263
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t244 : ((34282573407/1250000000000 : ℚ) : ℝ) ≤ stT301 244 := by
  have hc : ((428409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34282573407/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((428409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c245 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-709109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2948787/5000000) (δ := 3029/100000000) (ψ := 1041953/1000000) 301 263
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t245 : ((-453097318293/10000000000000 : ℚ) : ℝ) ≤ stT301 245 := by
  have hc : ((-709209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453097318293/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-709209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c246 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-903249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3372597/5000000) (δ := 7553/500000000) (ψ := 1041953/1000000) 301 264
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t246 : ((-575954545373/10000000000000 : ℚ) : ℝ) ≤ stT301 246 := by
  have hc : ((-903349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575954545373/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-903349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c247 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((46839/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -923113/2500000) (δ := 7553/500000000) (ψ := 1041953/1000000) 301 264
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t247 : ((7442773019/1250000000000 : ℚ) : ℝ) ≤ stT301 247 := by
  have hc : ((46789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7442773019/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((46789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c248 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((966179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -652051/10000000) (δ := 7553/500000000) (ψ := 1041953/1000000) 301 264
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t248 : ((122692033/2000000000 : ℚ) : ℝ) ≤ stT301 248 := by
  have hc : ((966079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122692033/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((966079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c249 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((58133/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594021/2500000) (δ := 7603/500000000) (ψ := 1041953/1000000) 301 264
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t249 : ((9208485013/250000000000 : ℚ) : ℝ) ≤ stT301 249 := by
  have hc : ((58123/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9208485013/250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((58123/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c250 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-69137/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269609/500000) (δ := 15197/1000000000) (ψ := 1041953/1000000) 301 264
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t250 : ((-10933504043/312500000000 : ℚ) : ℝ) ≤ stT301 250 := by
  have hc : ((-138299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10933504043/312500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-138299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c251 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-15259/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1827951/2500000) (δ := 15199/1000000000) (ψ := 1041953/1000000) 301 265
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t251 : ((-30823650391/500000000000 : ℚ) : ℝ) ≤ stT301 251 := by
  have hc : ((-244169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30823650391/500000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-244169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c252 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-156473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1079947/2500000) (δ := 3801/250000000) (ψ := 1041953/1000000) 301 265
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t252 : ((-98631752193/10000000000000 : ℚ) : ℝ) ≤ stT301 252 := by
  have hc : ((-156573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98631752193/10000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-156573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c253 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((859843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1339587/10000000) (δ := 3801/250000000) (ψ := 1041953/1000000) 301 265
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t253 : ((270257632821/5000000000000 : ℚ) : ℝ) ≤ stT301 253 := by
  have hc : ((859743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270257632821/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((859743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c254 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((159029/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13031/80000) (δ := 3801/250000000) (ψ := 1041953/1000000) 301 265
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t254 : ((19954198419/400000000000 : ℚ) : ℝ) ≤ stT301 254 := by
  have hc : ((159009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19954198419/400000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((159009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c255 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-52087/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4585673/10000000) (δ := 59/3906250) (ψ := 1041953/1000000) 301 265
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t255 : ((-1305228243/80000000000 : ℚ) : ℝ) ≤ stT301 255 := by
  have hc : ((-52107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1305228243/80000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-52107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c256 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-49583/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7530883/10000000) (δ := 3801/250000000) (ψ := 1041953/1000000) 301 265
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t256 : ((-7748137397/125000000000 : ℚ) : ℝ) ≤ stT301 256 := by
  have hc : ((-12397/12500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7748137397/125000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-12397/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c257 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-3141/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655423/1250000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 266
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t257 : ((-15677538139/500000000000 : ℚ) : ℝ) ≤ stT301 257 := by
  have hc : ((-25133/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15677538139/500000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-25133/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c258 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((5991/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46421/200000) (δ := 15211/1000000000) (ψ := 1041953/1000000) 301 266
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t258 : ((93230157/2500000000 : ℚ) : ℝ) ≤ stT301 258 := by
  have hc : ((599/1000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93230157/2500000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((599/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c259 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((972281/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147499/2500000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 266
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t259 : ((604083135789/10000000000000 : ℚ) : ℝ) ≤ stT301 259 := by
  have hc : ((972181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((604083135789/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((972181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c260 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((6959/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348983/1000000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 266
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t260 : ((862660643/80000000000 : ℚ) : ℝ) ≤ stT301 260 := by
  have hc : ((1391/8000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((862660643/80000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((1391/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c261 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-830839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6378527/10000000) (δ := 15111/1000000000) (ψ := 1041953/1000000) 301 266
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t261 : ((-102867755383/2000000000000 : ℚ) : ℝ) ≤ stT301 261 := by
  have hc : ((-830939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102867755383/2000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-830939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c262 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-846791/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6451801/10000000) (δ := 22609/500000000) (ψ := 1041953/1000000) 301 267
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t262 : ((-523211800473/10000000000000 : ℚ) : ℝ) ≤ stT301 262 := by
  have hc : ((-846891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523211800473/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-846891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c263 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((13631/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28009/78125) (δ := 7609/500000000) (ψ := 1041953/1000000) 301 267
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t263 : ((4199531373/500000000000 : ℚ) : ℝ) ≤ stT301 263 := by
  have hc : ((13621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4199531373/500000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((13621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c264 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((478873/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36467/500000) (δ := 9057/200000000) (ψ := 1041953/1000000) 301 267
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t264 : ((294694967111/5000000000000 : ℚ) : ℝ) ≤ stT301 264 := by
  have hc : ((478823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294694967111/5000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((478823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c265 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((82849/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2115637/10000000) (δ := 3017/200000000) (ψ := 1041953/1000000) 301 267
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t265 : ((20354419107/500000000000 : ℚ) : ℝ) ≤ stT301 265 := by
  have hc : ((165673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20354419107/500000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((165673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c266 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-99463/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 618741/1250000) (δ := 3037/200000000) (ψ := 1041953/1000000) 301 267
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t266 : ((-95312613/3906250000 : ℚ) : ℝ) ≤ stT301 266 := by
  have hc : ((-6218/15625 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95312613/3906250000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-6218/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c267 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-499741/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3886767/5000000) (δ := 3017/200000000) (ψ := 1041953/1000000) 301 267
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t267 : ((-305867593881/5000000000000 : ℚ) : ℝ) ≤ stT301 267 := by
  have hc : ((-499791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305867593881/5000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-499791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c268 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-459779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2560679/5000000) (δ := 7613/500000000) (ψ := 1041953/1000000) 301 268
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t268 : ((-8778630231/312500000000 : ℚ) : ℝ) ≤ stT301 268 := by
  have hc : ((-459879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8778630231/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-459879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c269 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((599837/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2318747/10000000) (δ := 7613/500000000) (ψ := 1041953/1000000) 301 268
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t269 : ((36566564627/1000000000000 : ℚ) : ℝ) ≤ stT301 269 := by
  have hc : ((599737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36566564627/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((599737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c270 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((982119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 473479/10000000) (δ := 15077/1000000000) (ψ := 1041953/1000000) 301 268
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t270 : ((29881856151/500000000000 : ℚ) : ℝ) ≤ stT301 270 := by
  have hc : ((982019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29881856151/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((982019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c271 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((132709/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813849/2500000) (δ := 15177/1000000000) (ψ := 1041953/1000000) 301 268
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t271 : ((2518265797/156250000000 : ℚ) : ℝ) ≤ stT301 271 := by
  have hc : ((132659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2518265797/156250000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((132659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c272 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-744647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506751/2500000) (δ := 15177/1000000000) (ψ := 1041953/1000000) 301 268
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t272 : ((-22578494799/500000000000 : ℚ) : ℝ) ≤ stT301 272 := by
  have hc : ((-744747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22578494799/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-744747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c273 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-930951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -691951/1000000) (δ := 1517/100000000) (ψ := 1041953/1000000) 301 269
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t273 : ((-140874533657/2500000000000 : ℚ) : ℝ) ≤ stT301 273 := by
  have hc : ((-931051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140874533657/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-931051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c274 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-48141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4168069/10000000) (δ := 1517/100000000) (ψ := 1041953/1000000) 301 269
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t274 : ((-29113291493/5000000000000 : ℚ) : ℝ) ≤ stT301 274 := by
  have hc : ((-48191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29113291493/5000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-48191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c275 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((168303/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -713393/5000000) (δ := 15233/1000000000) (ψ := 1041953/1000000) 301 269
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t275 : ((50739175613/1000000000000 : ℚ) : ℝ) ≤ stT301 275 := by
  have hc : ((168283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50739175613/1000000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((168283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c276 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((54181/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652319/5000000) (δ := 1507/100000000) (ψ := 1041953/1000000) 301 269
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t276 : ((130437412371/2500000000000 : ℚ) : ℝ) ≤ stT301 276 := by
  have hc : ((216699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130437412371/2500000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((216699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c277 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-1587/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 805241/2000000) (δ := 15133/1000000000) (ψ := 1041953/1000000) 301 269
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t277 : ((-477969811/200000000000 : ℚ) : ℝ) ≤ stT301 277 := by
  have hc : ((-1591/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-477969811/200000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-1591/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c278 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-180399/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3368957/5000000) (δ := 15133/1000000000) (ψ := 1041953/1000000) 301 269
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t278 : ((-108208279859/2000000000000 : ℚ) : ℝ) ≤ stT301 278 := by
  have hc : ((-180419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108208279859/2000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-180419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c279 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-805461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6268123/10000000) (δ := 15063/1000000000) (ψ := 1041953/1000000) 301 270
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t279 : ((-96455457457/2000000000000 : ℚ) : ℝ) ≤ stT301 279 := by
  have hc : ((-805561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96455457457/2000000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-805561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c280 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((140033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3575753/10000000) (δ := 757/50000000) (ψ := 1041953/1000000) 301 270
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t280 : ((41812959931/5000000000000 : ℚ) : ℝ) ≤ stT301 280 := by
  have hc : ((139933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41812959931/5000000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((139933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c281 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((936867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893091/10000000) (δ := 15163/1000000000) (ψ := 1041953/1000000) 301 270
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t281 : ((558827417083/10000000000000 : ℚ) : ℝ) ≤ stT301 281 := by
  have hc : ((936767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558827417083/10000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((936767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c282 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((757033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 178009/1000000) (δ := 15163/1000000000) (ψ := 1041953/1000000) 301 270
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t282 : ((450746789103/10000000000000 : ℚ) : ℝ) ≤ stT301 282 := by
  have hc : ((756933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450746789103/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((756933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c283 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-205251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 444379/1000000) (δ := 757/50000000) (ψ := 1041953/1000000) 301 270
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t283 : ((-122068643089/10000000000000 : ℚ) : ℝ) ≤ stT301 283 := by
  have hc : ((-205351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122068643089/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-205351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c284 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-190929/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3549079/5000000) (δ := 15163/1000000000) (ψ := 1041953/1000000) 301 270
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t284 : ((-113307418059/2000000000000 : ℚ) : ℝ) ≤ stT301 284 := by
  have hc : ((-190949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113307418059/2000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-190949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c285 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-363911/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5964843/10000000) (δ := 3789/250000000) (ψ := 1041953/1000000) 301 271
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t285 : ((-215591934389/5000000000000 : ℚ) : ℝ) ≤ stT301 285 := by
  have hc : ((-363961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215591934389/5000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-363961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c286 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((118449/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3329061/10000000) (δ := 941/62500000) (ψ := 1041953/1000000) 301 271
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t286 : ((4375671843/312500000000 : ℚ) : ℝ) ≤ stT301 286 := by
  have hc : ((118399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4375671843/312500000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((118399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c287 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((38431/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140507/2000000) (δ := 941/62500000) (ψ := 1041953/1000000) 301 271
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t287 : ((22682727987/400000000000 : ℚ) : ℝ) ≤ stT301 287 := by
  have hc : ((38427/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22682727987/400000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((38427/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c288 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((360371/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914811/10000000) (δ := 15247/1000000000) (ψ := 1041953/1000000) 301 271
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t288 : ((42464190171/1000000000000 : ℚ) : ℝ) ≤ stT301 288 := by
  have hc : ((360321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42464190171/1000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((360321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c289 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-236201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2261563/5000000) (δ := 941/62500000) (ψ := 1041953/1000000) 301 271
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t289 : ((-34750188759/2500000000000 : ℚ) : ℝ) ≤ stT301 289 := by
  have hc : ((-236301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34750188759/2500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-236301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c290 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-478749/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7122487/10000000) (δ := 15147/1000000000) (ψ := 1041953/1000000) 301 271
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t290 : ((-281160827579/5000000000000 : ℚ) : ℝ) ≤ stT301 290 := by
  have hc : ((-478799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281160827579/5000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-478799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c291 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-736081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2997573/5000000) (δ := 15149/1000000000) (ψ := 1041953/1000000) 301 272
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t291 : ((-431557400191/10000000000000 : ℚ) : ℝ) ≤ stT301 291 := by
  have hc : ((-736181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431557400191/10000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-736181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c292 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((203909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3413619/10000000) (δ := 7577/500000000) (ψ := 1041953/1000000) 301 272
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t292 : ((23854009169/2000000000000 : ℚ) : ℝ) ≤ stT301 292 := by
  have hc : ((203809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23854009169/2000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((203809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c293 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((943953/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210243/2500000) (δ := 7577/500000000) (ψ := 1041953/1000000) 301 272
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t293 : ((275702292859/5000000000000 : ℚ) : ℝ) ≤ stT301 293 := by
  have hc : ((943853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275702292859/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((943853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c294 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((192947/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172287/1000000) (δ := 15249/1000000000) (ψ := 1041953/1000000) 301 272
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t294 : ((56257116271/1250000000000 : ℚ) : ℝ) ≤ stT301 294 := by
  have hc : ((96461/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56257116271/1250000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((96461/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c295 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-69983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4278059/10000000) (δ := 15249/1000000000) (ψ := 1041953/1000000) 301 272
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t295 : ((-40774823359/5000000000000 : ℚ) : ℝ) ≤ stT301 295 := by
  have hc : ((-70033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40774823359/5000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-70033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c296 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-45821/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1364919/2000000) (δ := 7577/500000000) (ψ := 1041953/1000000) 301 272
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t296 : ((-13317929207/250000000000 : ℚ) : ℝ) ≤ stT301 296 := by
  have hc : ((-22913/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13317929207/250000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-22913/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c297 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-164679/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1586353/2500000) (δ := 15141/1000000000) (ψ := 1041953/1000000) 301 273
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t297 : ((-95568077041/2000000000000 : ℚ) : ℝ) ≤ stT301 297 := by
  have hc : ((-164699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95568077041/2000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-164699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c298 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((2773/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1908017/5000000) (δ := 15241/1000000000) (ψ := 1041953/1000000) 301 273
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t298 : ((1602734007/625000000000 : ℚ) : ℝ) ≤ stT301 298 := by
  have hc : ((11067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1602734007/625000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((11067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c299 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((173759/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295083/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 273
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t299 : ((50237848023/1000000000000 : ℚ) : ℝ) ≤ stT301 299 := by
  have hc : ((173739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50237848023/1000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((173739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c300 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((110469/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1217439/10000000) (δ := 7531/500000000) (ψ := 1041953/1000000) 301 273
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t300 : ((2550882411/50000000000 : ℚ) : ℝ) ≤ stT301 300 := by
  have hc : ((220913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2550882411/50000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((220913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c301 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((82061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465201/1250000) (δ := 15241/1000000000) (ψ := 1041953/1000000) 301 273
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t301 : ((4724150079/1000000000000 : ℚ) : ℝ) ≤ stT301 301 := by
  have hc : ((81961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4724150079/1000000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((81961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c302 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-49581/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2487/4000) (δ := 15241/1000000000) (ψ := 1041953/1000000) 301 273
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t302 : ((-28534288791/625000000000 : ℚ) : ℝ) ≤ stT301 302 := by
  have hc : ((-198349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28534288791/625000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-198349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c303 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-942603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218839/312500) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 274
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t303 : ((-108313746591/2000000000000 : ℚ) : ℝ) ≤ stT301 303 := by
  have hc : ((-942703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108313746591/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-942703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c304 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-236321/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1130859/2500000) (δ := 15069/1000000000) (ψ := 1041953/1000000) 301 274
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t304 : ((-6779845017/500000000000 : ℚ) : ℝ) ≤ stT301 304 := by
  have hc : ((-236421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6779845017/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-236421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c305 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((68157/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1026113/5000000) (δ := 15069/1000000000) (ψ := 1041953/1000000) 301 274
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t305 : ((19510417953/500000000000 : ℚ) : ℝ) ≤ stT301 305 := by
  have hc : ((68147/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19510417953/500000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((68147/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c306 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((246629/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411007/10000000) (δ := 7617/500000000) (ψ := 1041953/1000000) 301 274
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t306 : ((35243472311/625000000000 : ℚ) : ℝ) ≤ stT301 306 := by
  have hc : ((61651/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35243472311/625000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((61651/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c307 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((411729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1433057/5000000) (δ := 15069/1000000000) (ψ := 1041953/1000000) 301 274
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t307 : ((23492901917/1000000000000 : ℚ) : ℝ) ≤ stT301 307 := by
  have hc : ((411629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23492901917/1000000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((411629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c308 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-526519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1328311/2500000) (δ := 15069/1000000000) (ψ := 1041953/1000000) 301 274
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t308 : ((-300069086057/10000000000000 : ℚ) : ℝ) ≤ stT301 308 := by
  have hc : ((-526619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300069086057/10000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-526619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c309 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-124897/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7752473/10000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 274
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t309 : ((-142117282539/2500000000000 : ℚ) : ℝ) ≤ stT301 309 := by
  have hc : ((-249819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142117282539/2500000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-249819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c310 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-9317/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5524163/10000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 275
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t310 : ((-42340715157/1250000000000 : ℚ) : ℝ) ≤ stT301 310 := by
  have hc : ((-149097/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42340715157/1250000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-149097/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c311 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((12983/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1550293/5000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 275
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t311 : ((7359703013/400000000000 : ℚ) : ℝ) ≤ stT301 311 := by
  have hc : ((12979/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7359703013/400000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((12979/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c312 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((481353/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -684911/10000000) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 275
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t312 : ((136241958907/2500000000000 : ℚ) : ℝ) ≤ stT301 312 := by
  have hc : ((481303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136241958907/2500000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((481303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c313 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((192933/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1723089/10000000) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 275
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t313 : ((27259491891/625000000000 : ℚ) : ℝ) ≤ stT301 313 := by
  have hc : ((48227/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27259491891/625000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((48227/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c314 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-9811/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2061707/5000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 275
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t314 : ((-11087450451/2500000000000 : ℚ) : ℝ) ≤ stT301 314 := by
  have hc : ((-19647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11087450451/2500000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-19647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c315 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-860199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3258069/5000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 275
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t315 : ((-484724287663/10000000000000 : ℚ) : ℝ) ≤ stT301 315 := by
  have hc : ((-860299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484724287663/10000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-860299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c316 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-228383/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6806701/10000000) (δ := 15183/1000000000) (ψ := 1041953/1000000) 301 276
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t316 : ((-1003824609/19531250000 : ℚ) : ℝ) ≤ stT301 316 := by
  have hc : ((-28551/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1003824609/19531250000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-28551/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c317 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-199527/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2214589/5000000) (δ := 761/50000000) (ψ := 1041953/1000000) 301 276
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t317 : ((-14015212789/1250000000000 : ℚ) : ℝ) ≤ stT301 317 := by
  have hc : ((-199627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14015212789/1250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-199627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c318 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((339777/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64347/312500) (δ := 761/50000000) (ψ := 1041953/1000000) 301 276
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t318 : ((47627347311/1250000000000 : ℚ) : ℝ) ≤ stT301 318 := by
  have hc : ((339727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47627347311/1250000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((339727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c319 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((198527/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75899/2500000) (δ := 15083/1000000000) (ψ := 1041953/1000000) 301 276
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t319 : ((27785620311/500000000000 : ℚ) : ℝ) ≤ stT301 319 := by
  have hc : ((198507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27785620311/500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((198507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c320 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((485809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 265877/1000000) (δ := 761/50000000) (ψ := 1041953/1000000) 301 276
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t320 : ((33939887793/1250000000000 : ℚ) : ℝ) ≤ stT301 320 := by
  have hc : ((485709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33939887793/1250000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((485709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c321 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-41859/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5006721/10000000) (δ := 15083/1000000000) (ψ := 1041953/1000000) 301 276
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t321 : ((-11684507437/500000000000 : ℚ) : ℝ) ≤ stT301 321 := by
  have hc : ((-41869/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11684507437/500000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-41869/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c322 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-244883/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7347297/10000000) (δ := 15083/1000000000) (ψ := 1041953/1000000) 301 276
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t322 : ((-34120521333/625000000000 : ℚ) : ℝ) ≤ stT301 322 := by
  have hc : ((-61227/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34120521333/625000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-61227/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c323 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-744729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3013657/5000000) (δ := 1519/100000000) (ψ := 1041953/1000000) 301 277
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t323 : ((-82886805607/2000000000000 : ℚ) : ℝ) ≤ stT301 323 := by
  have hc : ((-744829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82886805607/2000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-744829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c324 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((90199/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1850593/5000000) (δ := 1519/100000000) (ψ := 1041953/1000000) 301 277
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t324 : ((10010989989/2000000000000 : ℚ) : ℝ) ≤ stT301 324 := by
  have hc : ((90099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10010989989/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((90099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c325 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((425499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -691141/5000000) (δ := 1519/100000000) (ψ := 1041953/1000000) 301 277
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t325 : ((2359965603/50000000000 : ℚ) : ℝ) ≤ stT301 325 := by
  have hc : ((425449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2359965603/50000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((425449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c326 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((232917/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232387/2500000) (δ := 15113/1000000000) (ψ := 1041953/1000000) 301 277
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t326 : ((4030836513/78125000000 : ℚ) : ℝ) ≤ stT301 326 := by
  have hc : ((58223/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4030836513/78125000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((58223/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c327 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((273543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646861/2000000) (δ := 15113/1000000000) (ψ := 1041953/1000000) 301 277
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t327 : ((151214252443/10000000000000 : ℚ) : ℝ) ≤ stT301 327 := by
  have hc : ((273443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151214252443/10000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((273443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c328 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-299411/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172877/312500) (δ := 1509/100000000) (ψ := 1041953/1000000) 301 277
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t328 : ((-82674893419/2500000000000 : ℚ) : ℝ) ≤ stT301 328 := by
  have hc : ((-299461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82674893419/2500000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-299461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c329 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-499961/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7822749/10000000) (δ := 15113/1000000000) (ψ := 1041953/1000000) 301 277
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t329 : ((-137832532249/2500000000000 : ℚ) : ℝ) ≤ stT301 329 := by
  have hc : ((-500011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137832532249/2500000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-500011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c330 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-620817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1400363/2500000) (δ := 7553/500000000) (ψ := 1041953/1000000) 301 278
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t330 : ((-170901815997/5000000000000 : ℚ) : ℝ) ≤ stT301 330 := by
  have hc : ((-620917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170901815997/5000000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-620917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c331 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((119313/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3324613/10000000) (δ := 7603/500000000) (ψ := 1041953/1000000) 301 278
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t331 : ((65552788687/5000000000000 : ℚ) : ℝ) ≤ stT301 331 := by
  have hc : ((119263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65552788687/5000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((119263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c332 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((456167/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1054621/10000000) (δ := 15097/1000000000) (ψ := 1041953/1000000) 301 278
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t332 : ((250326588057/5000000000000 : ℚ) : ℝ) ≤ stT301 332 := by
  have hc : ((456117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250326588057/5000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((456117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c333 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((177083/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1208523/10000000) (δ := 15197/1000000000) (ψ := 1041953/1000000) 301 278
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t333 : ((24257453937/500000000000 : ℚ) : ℝ) ≤ stT301 333 := by
  have hc : ((177063/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24257453937/500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((177063/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c334 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((45947/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1732447/5000000) (δ := 15097/1000000000) (ψ := 1041953/1000000) 301 278
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t334 : ((502547407/50000000000 : ℚ) : ℝ) ≤ stT301 334 := by
  have hc : ((22961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502547407/50000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((22961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c335 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-655641/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714321/1250000) (δ := 15097/1000000000) (ψ := 1041953/1000000) 301 278
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t335 : ((-358269997019/10000000000000 : ℚ) : ℝ) ≤ stT301 335 := by
  have hc : ((-655741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358269997019/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-655741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c336 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-999143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3875247/5000000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 279
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t336 : ((-109026404487/2000000000000 : ℚ) : ℝ) ≤ stT301 336 := by
  have hc : ((-999243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109026404487/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-999243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c337 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-9267/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2757107/5000000) (δ := 3041/200000000) (ψ := 1041953/1000000) 301 279
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t337 : ((-16156513259/500000000000 : ℚ) : ℝ) ≤ stT301 337 := by
  have hc : ((-148297/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16156513259/500000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-148297/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c338 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((127063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -410579/1250000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 279
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t338 : ((8635740883/625000000000 : ℚ) : ℝ) ≤ stT301 338 := by
  have hc : ((127013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8635740883/625000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((127013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c339 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((1139/1250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1061521/10000000) (δ := 3041/200000000) (ψ := 1041953/1000000) 301 279
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t339 : ((7917459/160000000 : ℚ) : ℝ) ≤ stT301 339 := by
  have hc : ((9111/10000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7917459/160000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((9111/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c340 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((895169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154967/10000000) (δ := 7599/500000000) (ψ := 1041953/1000000) 301 279
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t340 : ((242709595247/5000000000000 : ℚ) : ℝ) ≤ stT301 340 := by
  have hc : ((895069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242709595247/5000000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((895069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c341 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((222943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3364909/10000000) (δ := 7599/500000000) (ψ := 1041953/1000000) 301 279
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t341 : ((12067616979/1000000000000 : ℚ) : ℝ) ≤ stT301 341 := by
  have hc : ((222843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12067616979/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((222843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c342 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-38151/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113691/2000000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 279
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t342 : ((-82532452831/2500000000000 : ℚ) : ℝ) ≤ stT301 342 := by
  have hc : ((-152629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82532452831/2500000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-152629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c343 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-499687/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7765529/10000000) (δ := 7599/500000000) (ψ := 1041953/1000000) 301 279
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t343 : ((-5396659863/100000000000 : ℚ) : ℝ) ≤ stT301 343 := by
  have hc : ((-499737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5396659863/100000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-499737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c344 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-1667/2500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1437939/2500000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 280
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t344 : ((-898921179/25000000000 : ℚ) : ℝ) ≤ stT301 344 := by
  have hc : ((-6669/10000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898921179/25000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-6669/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c345 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((143341/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3567399/10000000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 280
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t345 : ((77118232821/10000000000000 : ℚ) : ℝ) ≤ stT301 345 := by
  have hc : ((143241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77118232821/10000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((143241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c346 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((212373/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694719/5000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 280
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t346 : ((28539730461/625000000000 : ℚ) : ℝ) ≤ stT301 346 := by
  have hc : ((53087/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28539730461/625000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((53087/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c347 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((475721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 782277/10000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 280
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t347 : ((63838377897/1250000000000 : ℚ) : ℝ) ≤ stT301 347 := by
  have hc : ((475671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63838377897/1250000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((475671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c348 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((190879/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473873/5000000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 280
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t348 : ((12786878803/625000000000 : ℚ) : ℝ) ≤ stT301 348 := by
  have hc : ((190829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12786878803/625000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((190829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c349 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-14209/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021409/2000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 280
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t349 : ((-7607579967/312500000000 : ℚ) : ℝ) ≤ stT301 349 := by
  have hc : ((-113697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7607579967/312500000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-113697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c350 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-971917/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3630049/5000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 280
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t350 : ((-519565442891/10000000000000 : ℚ) : ℝ) ≤ stT301 350 := by
  have hc : ((-972017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519565442891/10000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-972017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c351 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-813163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1575227/2500000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 281
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t351 : ((-434088072143/10000000000000 : ℚ) : ℝ) ≤ stT301 351 := by
  have hc : ((-813263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434088072143/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-813263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c352 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-93117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104003/250000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 281
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t352 : ((-24842423717/5000000000000 : ℚ) : ℝ) ≤ stT301 352 := by
  have hc : ((-93217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24842423717/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-93217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c353 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((172349/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2025353/10000000) (δ := 15119/1000000000) (ψ := 1041953/1000000) 301 281
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t353 : ((11464844963/312500000000 : ℚ) : ℝ) ≤ stT301 353 := by
  have hc : ((43081/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11464844963/312500000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((43081/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c354 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((199829/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51697/5000000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 281
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t354 : ((53098642323/1000000000000 : ℚ) : ℝ) ≤ stT301 354 := by
  have hc : ((199809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53098642323/1000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((199809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c355 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((629087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113023/5000000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 281
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t355 : ((41728884541/1250000000000 : ℚ) : ℝ) ≤ stT301 355 := by
  have hc : ((628987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41728884541/1250000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((628987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c356 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-165569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4342829/10000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 281
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t356 : ((-87804404331/10000000000000 : ℚ) : ℝ) ≤ stT301 356 := by
  have hc : ((-165669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87804404331/10000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-165669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c357 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-211793/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6453591/10000000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 281
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t357 : ((-56053079613/1250000000000 : ℚ) : ℝ) ≤ stT301 357 := by
  have hc : ((-105909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56053079613/1250000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-105909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c358 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-240139/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7149479/10000000) (δ := 7563/500000000) (ψ := 1041953/1000000) 301 282
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t358 : ((-31732689197/625000000000 : ℚ) : ℝ) ≤ stT301 358 := by
  have hc : ((-60041/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31732689197/625000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-60041/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c359 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-434413/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -631307/1250000) (δ := 15177/1000000000) (ψ := 1041953/1000000) 301 282
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t359 : ((-11466363557/500000000000 : ℚ) : ℝ) ≤ stT301 359 := by
  have hc : ((-434513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11466363557/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-434513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c360 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((378251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1478613/5000000) (δ := 7613/500000000) (ψ := 1041953/1000000) 301 282
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t360 : ((99651485973/5000000000000 : ℚ) : ℝ) ≤ stT301 360 := by
  have hc : ((378151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99651485973/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((378151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c361 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((37603/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869867/10000000) (δ := 15177/1000000000) (ψ := 1041953/1000000) 301 282
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t361 : ((3957783537/80000000000 : ℚ) : ℝ) ≤ stT301 361 := by
  have hc : ((37599/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3957783537/80000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((37599/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c362 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((88481/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 605887/5000000) (δ := 15077/1000000000) (ψ := 1041953/1000000) 301 282
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t362 : ((11624823987/250000000000 : ℚ) : ℝ) ≤ stT301 362 := by
  have hc : ((88471/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11624823987/250000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((88471/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c363 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((252969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3287621/10000000) (δ := 7613/500000000) (ψ := 1041953/1000000) 301 282
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t363 : ((132721581947/10000000000000 : ℚ) : ℝ) ≤ stT301 363 := by
  have hc : ((252869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132721581947/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((252869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c364 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-541569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1339437/2500000) (δ := 15077/1000000000) (ψ := 1041953/1000000) 301 282
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t364 : ((-283912014667/10000000000000 : ℚ) : ℝ) ≤ stT301 364 := by
  have hc : ((-541669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283912014667/10000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-541669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c365 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-246281/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927779/1250000) (δ := 7563/500000000) (ψ := 1041953/1000000) 301 282
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t365 : ((-2014413621/39062500000 : ℚ) : ℝ) ≤ stT301 365 := by
  have hc : ((-123153/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2014413621/39062500000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-123153/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c366 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-795577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6226891/10000000) (δ := 15233/1000000000) (ψ := 1041953/1000000) 301 283
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t366 : ((-415907528993/10000000000000 : ℚ) : ℝ) ≤ stT301 366 := by
  have hc : ((-795677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415907528993/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-795677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c367 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-49261/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834739/2000000) (δ := 15133/1000000000) (ψ := 1041953/1000000) 301 283
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t367 : ((-6435036189/1250000000000 : ℚ) : ℝ) ≤ stT301 367 := by
  have hc : ((-49311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6435036189/1250000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-49311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c368 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((329831/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2126067/10000000) (δ := 15233/1000000000) (ψ := 1041953/1000000) 301 283
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t368 : ((85955109183/2500000000000 : ℚ) : ℝ) ≤ stT301 368 := by
  have hc : ((329781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85955109183/2500000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((329781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c369 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((199887/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10501/1250000) (δ := 15133/1000000000) (ψ := 1041953/1000000) 301 283
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t369 : ((104046562993/2000000000000 : ℚ) : ℝ) ≤ stT301 369 := by
  have hc : ((199867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104046562993/2000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((199867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c370 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((355097/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976279/5000000) (δ := 15133/1000000000) (ψ := 1041953/1000000) 301 283
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t370 : ((1476640473/40000000000 : ℚ) : ℝ) ≤ stT301 370 := by
  have hc : ((355047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1476640473/40000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((355047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c371 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-707/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 796711/2000000) (δ := 1517/100000000) (ψ := 1041953/1000000) 301 283
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t371 : ((-117977327/100000000000 : ℚ) : ℝ) ≤ stT301 371 := by
  have hc : ((-5681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117977327/100000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-5681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c372 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-739857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1201827/2000000) (δ := 15133/1000000000) (ψ := 1041953/1000000) 301 283
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t372 : ((-95912486383/2500000000000 : ℚ) : ℝ) ≤ stT301 372 := by
  have hc : ((-739957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95912486383/2500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-739957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c373 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-498771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7678667/10000000) (δ := 7531/500000000) (ψ := 1041953/1000000) 301 284
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t373 : ((-258280036201/5000000000000 : ℚ) : ℝ) ≤ stT301 373 := by
  have hc : ((-498821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258280036201/5000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-498821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c374 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-320117/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5663999/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 284
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t374 : ((-5173578553/156250000000 : ℚ) : ℝ) ≤ stT301 374 := by
  have hc : ((-320167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5173578553/156250000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-320167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c375 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((54371/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1827299/5000000) (δ := 7531/500000000) (ψ := 1041953/1000000) 301 284
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t375 : ((28051201437/5000000000000 : ℚ) : ℝ) ≤ stT301 375 := by
  have hc : ((54321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28051201437/5000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((54321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c376 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((789841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330123/2000000) (δ := 15141/1000000000) (ψ := 1041953/1000000) 301 284
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t376 : ((40727733111/1000000000000 : ℚ) : ℝ) ≤ stT301 376 := by
  have hc : ((789741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40727733111/1000000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((789741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c377 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((495163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13921/400000) (δ := 15141/1000000000) (ψ := 1041953/1000000) 301 284
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t377 : ((127498033969/2500000000000 : ℚ) : ℝ) ≤ stT301 377 := by
  have hc : ((495113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127498033969/2500000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((495113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c378 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((592563/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2341397/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 284
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t378 : ((38091223659/1250000000000 : ℚ) : ℝ) ≤ stT301 378 := by
  have hc : ((592463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38091223659/1250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((592463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c379 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-8017/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2164789/5000000) (δ := 15241/1000000000) (ψ := 1041953/1000000) 301 284
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t379 : ((-1030157163/125000000000 : ℚ) : ℝ) ≤ stT301 379 := by
  have hc : ((-4011/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1030157163/125000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-4011/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c380 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-407917/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1262483/2000000) (δ := 7531/500000000) (ψ := 1041953/1000000) 301 284
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t380 : ((-20928299133/500000000000 : ℚ) : ℝ) ≤ stT301 380 := by
  have hc : ((-407967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20928299133/500000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-407967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c381 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-39393/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7417903/10000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t381 : ((-5045928363/100000000000 : ℚ) : ℝ) ≤ stT301 381 := by
  have hc : ((-39397/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5045928363/100000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-39397/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c382 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-71337/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43563/80000) (δ := 3031/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t382 : ((-14602245971/500000000000 : ℚ) : ℝ) ≤ stT301 382 := by
  have hc : ((-142699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14602245971/500000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-142699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c383 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((44647/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1739057/5000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t383 : ((11133189/1220703125 : ℚ) : ℝ) ≤ stT301 383 := by
  have hc : ((22311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11133189/1220703125 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((22311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c384 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((821729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303179/2000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t384 : ((41928549499/1000000000000 : ℚ) : ℝ) ≤ stT301 384 := by
  have hc : ((821629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41928549499/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((821629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c385 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((984467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441207/10000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t385 : ((501679688449/10000000000000 : ℚ) : ℝ) ≤ stT301 385 := by
  have hc : ((984367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501679688449/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((984367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c386 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((575749/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 299149/1250000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t386 : ((146498640957/5000000000000 : ℚ) : ℝ) ≤ stT301 386 := by
  have hc : ((575649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146498640957/5000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((575649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c387 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-82253/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 868027/2000000) (δ := 3031/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t387 : ((-41837001687/5000000000000 : ℚ) : ℝ) ≤ stT301 387 := by
  have hc : ((-82303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41837001687/5000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-82303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c388 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-161753/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49079/78125) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 285
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t388 : ((-41063973001/1000000000000 : ℚ) : ℝ) ≤ stT301 388 := by
  have hc : ((-161773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41063973001/1000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-161773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c389 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-989357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1872229/2500000) (δ := 3031/200000000) (ψ := 1041953/1000000) 301 286
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t389 : ((-501675477597/10000000000000 : ℚ) : ℝ) ≤ stT301 389 := by
  have hc : ((-989457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501675477597/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-989457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c390 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-151691/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1389237/2500000) (δ := 3787/250000000) (ψ := 1041953/1000000) 301 286
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t390 : ((-1920610773/62500000000 : ℚ) : ℝ) ≤ stT301 390 := by
  have hc : ((-37929/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1920610773/62500000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-37929/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c391 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((118539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1814973/5000000) (δ := 3787/250000000) (ψ := 1041953/1000000) 301 286
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t391 : ((59897089519/10000000000000 : ℚ) : ℝ) ≤ stT301 391 := by
  have hc : ((118439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59897089519/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((118439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c392 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((387799/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341567/2000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 286
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t392 : ((48960678481/1250000000000 : ℚ) : ℝ) ≤ stT301 392 := by
  have hc : ((387749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48960678481/1250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((387749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c393 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((199299/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26173/1250000) (δ := 953/62500000) (ψ := 1041953/1000000) 301 286
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t393 : ((100522903807/2000000000000 : ℚ) : ℝ) ≤ stT301 393 := by
  have hc : ((199279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100522903807/2000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((199279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c394 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((66097/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2121713/10000000) (δ := 3031/200000000) (ψ := 1041953/1000000) 301 286
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t394 : ((2080881369/62500000000 : ℚ) : ℝ) ≤ stT301 394 := by
  have hc : ((66087/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2080881369/62500000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((66087/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c395 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-10213/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80583/200000) (δ := 3031/200000000) (ψ := 1041953/1000000) 301 286
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t395 : ((-515130089/250000000000 : ℚ) : ℝ) ≤ stT301 395 := by
  have hc : ((-5119/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515130089/250000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-5119/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c396 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-179677/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2965923/5000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 286
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t396 : ((-45151834669/1250000000000 : ℚ) : ℝ) ≤ stT301 396 := by
  have hc : ((-89851/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45151834669/1250000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-89851/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c397 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-999953/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7829651/10000000) (δ := 3011/200000000) (ψ := 1041953/1000000) 301 286
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t397 : ((-250956299979/5000000000000 : ℚ) : ℝ) ≤ stT301 397 := by
  have hc : ((-1000053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250956299979/5000000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-1000053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c398 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-5867/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5985173/10000000) (δ := 15141/1000000000) (ψ := 1041953/1000000) 301 287
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t398 : ((-2941264089/80000000000 : ℚ) : ℝ) ≤ stT301 398 := by
  have hc : ((-29339/40000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2941264089/80000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-29339/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c399 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-67891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4096849/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 287
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t399 : ((-34038130357/10000000000000 : ℚ) : ℝ) ≤ stT301 399 := by
  have hc : ((-67991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34038130357/10000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-67991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c400 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((158263/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2213267/10000000) (δ := 15241/1000000000) (ψ := 1041953/1000000) 301 287
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t400 : ((79119/2500000 : ℚ) : ℝ) ≤ stT301 400 := by
  have hc : ((79119/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79119/2500000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((79119/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c401 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((99107/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334349/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 287
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t401 : ((3092916467/62500000000 : ℚ) : ℝ) ≤ stT301 401 := by
  have hc : ((99097/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3092916467/62500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((99097/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c402 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((204059/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1539827/10000000) (δ := 15141/1000000000) (ψ := 1041953/1000000) 301 287
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t402 : ((25440693409/625000000000 : ℚ) : ℝ) ≤ stT301 402 := by
  have hc : ((102017/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25440693409/625000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((102017/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c403 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((41111/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3409413/10000000) (δ := 15241/1000000000) (ψ := 1041953/1000000) 301 287
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t403 : ((4093773057/400000000000 : ℚ) : ℝ) ≤ stT301 403 := by
  have hc : ((41091/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4093773057/400000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((41091/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c404 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-64153/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2637167/5000000) (δ := 15141/1000000000) (ψ := 1041953/1000000) 301 287
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t404 : ((-63847110789/2500000000000 : ℚ) : ℝ) ≤ stT301 404 := by
  have hc : ((-128331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63847110789/2500000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-128331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c405 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-958891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1426933/2000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 287
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t405 : ((-59565807983/1250000000000 : ℚ) : ℝ) ≤ stT301 405 := by
  have hc : ((-958991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59565807983/1250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-958991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c406 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-17969/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3358779/5000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t406 : ((-2229715883/50000000000 : ℚ) : ℝ) ≤ stT301 406 := by
  have hc : ((-17971/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2229715883/50000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-17971/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c407 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-183493/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608301/1250000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t407 : ((-45489480663/2500000000000 : ℚ) : ℝ) ≤ stT301 407 := by
  have hc : ((-183543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45489480663/2500000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-183543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c408 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((14199/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3019773/10000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t408 : ((1405512247/80000000000 : ℚ) : ℝ) ≤ stT301 408 := by
  have hc : ((2839/8000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1405512247/80000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((2839/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c409 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((891087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1177653/10000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t409 : ((110141139979/2500000000000 : ℚ) : ℝ) ≤ stT301 409 := by
  have hc : ((890987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110141139979/2500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((890987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c410 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((965359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41247/625000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t410 : ((59588333847/1250000000000 : ℚ) : ℝ) ≤ stT301 410 := by
  have hc : ((965259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59588333847/1250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((965259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c411 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((542617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2493117/10000000) (δ := 15069/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t411 : ((267603562971/10000000000000 : ℚ) : ℝ) ≤ stT301 411 := by
  have hc : ((542517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267603562971/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((542517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c412 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-31451/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4321767/10000000) (δ := 7567/500000000) (ψ := 1041953/1000000) 301 288
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t412 : ((-3100932043/400000000000 : ℚ) : ℝ) ≤ stT301 412 := by
  have hc : ((-31471/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3100932043/400000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-31471/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c413 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-193889/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3072989/5000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 288
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t413 : ((-11927359269/312500000000 : ℚ) : ℝ) ≤ stT301 413 := by
  have hc : ((-96957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11927359269/312500000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-96957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c414 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-998999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387107/500000) (δ := 15227/1000000000) (ψ := 1041953/1000000) 301 289
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t414 : ((-245515590963/5000000000000 : ℚ) : ℝ) ≤ stT301 414 := by
  have hc : ((-999099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245515590963/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-999099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c415 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-717263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2963329/5000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 289
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t415 : ((-352139866803/10000000000000 : ℚ) : ℝ) ≤ stT301 415 := by
  have hc : ((-717363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352139866803/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-717363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c416 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-75379/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128613/312500) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 289
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t416 : ((-37006674389/10000000000000 : ℚ) : ℝ) ≤ stT301 416 := by
  have hc : ((-75479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37006674389/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-75479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c417 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((120599/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18038/78125) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 289
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t417 : ((29523888729/1000000000000 : ℚ) : ℝ) ≤ stT301 417 := by
  have hc : ((120579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29523888729/1000000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((120579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c418 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((979549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126619/2500000) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 289
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t418 : ((95812639527/2000000000000 : ℚ) : ℝ) ≤ stT301 418 := by
  have hc : ((979449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95812639527/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((979449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c419 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((869479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1291623/10000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 289
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t419 : ((424718592249/10000000000000 : ℚ) : ℝ) ≤ stT301 419 := by
  have hc : ((869379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424718592249/10000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((869379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c420 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((165151/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385679/1250000) (δ := 15227/1000000000) (ψ := 1041953/1000000) 301 289
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t420 : ((1611220659/100000000000 : ℚ) : ℝ) ≤ stT301 420 := by
  have hc : ((165101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1611220659/100000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((165101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c421 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-370163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4874953/10000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 289
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t421 : ((-180455448573/10000000000000 : ℚ) : ℝ) ≤ stT301 421 := by
  have hc : ((-370263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180455448573/10000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-370263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c422 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-111019/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6660259/10000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 289
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t422 : ((-108098713959/2500000000000 : ℚ) : ℝ) ≤ stT301 422 := by
  have hc : ((-222063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108098713959/2500000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-222063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c423 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-972533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7266687/10000000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 290
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t423 : ((-472910699361/10000000000000 : ℚ) : ℝ) ≤ stT301 423 := by
  have hc : ((-972633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472910699361/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-972633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c424 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-1463/2500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5489809/10000000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 290
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t424 : ((-2842468479/100000000000 : ℚ) : ℝ) ≤ stT301 424 := by
  have hc : ((-5853/10000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2842468479/100000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-5853/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c425 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((262/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -743429/2000000) (δ := 15119/1000000000) (ψ := 1041953/1000000) 301 290
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t425 : ((2030992277/500000000000 : ℚ) : ℝ) ≤ stT301 425 := by
  have hc : ((4187/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2030992277/500000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((4187/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c426 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((355651/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1948619/10000000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 290
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t426 : ((172289040101/5000000000000 : ℚ) : ℝ) ≤ stT301 426 := by
  have hc : ((355601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172289040101/5000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((355601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c427 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((498643/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184233/10000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 290
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t427 : ((241285606269/5000000000000 : ℚ) : ℝ) ≤ stT301 427 := by
  have hc : ((498593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241285606269/5000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((498593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c428 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((403903/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78797/500000) (δ := 15119/1000000000) (ψ := 1041953/1000000) 301 290
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t428 : ((24401202113/625000000000 : ℚ) : ℝ) ≤ stT301 428 := by
  have hc : ((403853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24401202113/625000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((403853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c429 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((235707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26657/80000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 290
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t429 : ((28438000507/2500000000000 : ℚ) : ℝ) ≤ stT301 429 := by
  have hc : ((235607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28438000507/2500000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((235607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c430 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-446519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508417/1000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 290
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t430 : ((-215378886417/10000000000000 : ℚ) : ℝ) ≤ stT301 430 := by
  have hc : ((-446619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215378886417/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-446619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c431 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-458807/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6832077/10000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 290
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t431 : ((-55256018797/1250000000000 : ℚ) : ℝ) ≤ stT301 431 := by
  have hc : ((-458857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55256018797/1250000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-458857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c432 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-191717/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7131967/10000000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 291
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t432 : ((-46124827931/1000000000000 : ℚ) : ℝ) ≤ stT301 432 := by
  have hc : ((-191737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46124827931/1000000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-191737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c433 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-69131/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5392037/10000000) (δ := 3803/250000000) (ψ := 1041953/1000000) 301 291
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t433 : ((-6645658359/250000000000 : ℚ) : ℝ) ≤ stT301 433 := by
  have hc : ((-138287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6645658359/250000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-138287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c434 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((108117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -365617/1000000) (δ := 3803/250000000) (ψ := 1041953/1000000) 301 291
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t434 : ((10369956051/2000000000000 : ℚ) : ℝ) ≤ stT301 434 := by
  have hc : ((108017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10369956051/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((108017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c435 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((179527/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1924291/10000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 291
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t435 : ((43032283713/1250000000000 : ℚ) : ℝ) ≤ stT301 435 := by
  have hc : ((89751/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43032283713/1250000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((89751/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c436 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((249229/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -491/25000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 291
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t436 : ((29836758813/625000000000 : ℚ) : ℝ) ≤ stT301 436 := by
  have hc : ((62301/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29836758813/625000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((62301/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c437 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((409537/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 763751/5000000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 291
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t437 : ((48970959817/1250000000000 : ℚ) : ℝ) ≤ stT301 437 := by
  have hc : ((409487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48970959817/1250000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((409487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c438 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((268437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1623783/5000000) (δ := 3803/250000000) (ψ := 1041953/1000000) 301 291
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t438 : ((64108124333/5000000000000 : ℚ) : ℝ) ≤ stT301 438 := by
  have hc : ((268337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64108124333/5000000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((268337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c439 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-1259/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4963643/10000000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 291
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t439 : ((-4808296913/250000000000 : ℚ) : ℝ) ≤ stT301 439 := by
  have hc : ((-20149/50000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4808296913/250000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-20149/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c440 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-55687/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3337903/5000000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 291
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t440 : ((-26550754459/625000000000 : ℚ) : ℝ) ≤ stT301 440 := by
  have hc : ((-222773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26550754459/625000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-222773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c441 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-488803/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7323907/10000000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 292
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t441 : ((-232787398923/5000000000000 : ℚ) : ℝ) ≤ stT301 441 := by
  have hc : ((-488853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232787398923/5000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-488853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c442 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-626459/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123899/2000000) (δ := 3041/200000000) (ψ := 1041953/1000000) 301 292
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t442 : ((-74506010367/2500000000000 : ℚ) : ℝ) ≤ stT301 442 := by
  have hc : ((-626559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74506010367/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-626559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c443 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((807/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97973/250000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 292
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t443 : ((92884787/625000000000 : ℚ) : ℝ) ≤ stT301 443 := by
  have hc : ((391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92884787/625000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c444 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((630287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2222183/10000000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 292
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t444 : ((149536443043/5000000000000 : ℚ) : ℝ) ≤ stT301 444 := by
  have hc : ((630187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149536443043/5000000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((630187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c445 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((122209/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132321/2500000) (δ := 3041/200000000) (ψ := 1041953/1000000) 301 292
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t445 : ((23170655937/500000000000 : ℚ) : ℝ) ≤ stT301 445 := by
  have hc : ((244393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23170655937/500000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((244393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c446 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((111787/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1159853/10000000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 292
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t446 : ((105853357637/2500000000000 : ℚ) : ℝ) ≤ stT301 446 := by
  have hc : ((223549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105853357637/2500000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((223549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c447 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((104839/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88911/312500) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 292
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t447 : ((24787620081/1250000000000 : ℚ) : ℝ) ≤ stT301 447 := by
  have hc : ((52407/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24787620081/1250000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((52407/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c448 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-118807/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1131691/2500000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 292
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t448 : ((-7019337849/625000000000 : ℚ) : ℝ) ≤ stT301 448 := by
  have hc : ((-118857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7019337849/625000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-118857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c449 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-790129/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3102269/5000000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 292
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t449 : ((-37293277197/1000000000000 : ℚ) : ℝ) ≤ stT301 449 := by
  have hc : ((-790229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37293277197/1000000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-790229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c450 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-999951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7829339/10000000) (δ := 7599/500000000) (ψ := 1041953/1000000) 301 293
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t450 : ((-94285808331/2000000000000 : ℚ) : ℝ) ≤ stT301 450 := by
  have hc : ((-1000051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94285808331/2000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-1000051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c451 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-389409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6158939/10000000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 293
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t451 : ((-91694616419/2500000000000 : ℚ) : ℝ) ≤ stT301 451 := by
  have hc : ((-389459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91694616419/2500000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-389459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c452 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-112101/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2246151/5000000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 293
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t452 : ((-52751456511/5000000000000 : ℚ) : ℝ) ≤ stT301 452 := by
  have hc : ((-112151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52751456511/5000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-112151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c453 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((53139/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2829277/10000000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 293
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t453 : ((624023869/31250000000 : ℚ) : ℝ) ≤ stT301 453 := by
  have hc : ((106253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((624023869/31250000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((106253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c454 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((89247/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234003/2000000) (δ := 7599/500000000) (ψ := 1041953/1000000) 301 293
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t454 : ((41880976551/1000000000000 : ℚ) : ℝ) ≤ stT301 454 := by
  have hc : ((89237/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41880976551/1000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((89237/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c455 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((490593/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 485711/10000000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 293
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t455 : ((229969992201/5000000000000 : ℚ) : ℝ) ≤ stT301 455 := by
  have hc : ((490543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229969992201/5000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((490543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c456 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((656143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8551/40000) (δ := 3041/200000000) (ψ := 1041953/1000000) 301 293
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t456 : ((76804922139/2500000000000 : ℚ) : ℝ) ≤ stT301 456 := by
  have hc : ((656043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76804922139/2500000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((656043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c457 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((28163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3786101/10000000) (δ := 3021/200000000) (ψ := 1041953/1000000) 301 293
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t457 : ((657534957/250000000000 : ℚ) : ℝ) ≤ stT301 457 := by
  have hc : ((28113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((657534957/250000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((28113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c458 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-565937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1086183/2000000) (δ := 7599/500000000) (ψ := 1041953/1000000) 301 293
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t458 : ((-26449210899/1000000000000 : ℚ) : ℝ) ≤ stT301 458 := by
  have hc : ((-566037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26449210899/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-566037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c459 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-475751/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7072193/10000000) (δ := 7549/500000000) (ψ := 1041953/1000000) 301 293
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t459 : ((-222085350561/5000000000000 : ℚ) : ℝ) ≤ stT301 459 := by
  have hc : ((-475801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222085350561/5000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-475801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c460 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-470989/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349909/500000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 294
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t460 : ((-219623346867/5000000000000 : ℚ) : ℝ) ≤ stT301 460 := by
  have hc : ((-471039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219623346867/5000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-471039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c461 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-543687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5364051/10000000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 294
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t461 : ((-253267163889/10000000000000 : ℚ) : ℝ) ≤ stT301 461 := by
  have hc : ((-543787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253267163889/10000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-543787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c462 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((38653/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1866767/5000000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 294
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t462 : ((8979868463/2500000000000 : ℚ) : ℝ) ≤ stT301 462 := by
  have hc : ((38603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8979868463/2500000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((38603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c463 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((665531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053239/5000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 294
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t463 : ((309251737509/10000000000000 : ℚ) : ℝ) ≤ stT301 463 := by
  have hc : ((665431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309251737509/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((665431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c464 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((490699/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482959/10000000) (δ := 3803/250000000) (ψ := 1041953/1000000) 301 294
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t464 : ((113888955231/2500000000000 : ℚ) : ℝ) ≤ stT301 464 := by
  have hc : ((490649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113888955231/2500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((490649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c465 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((224583/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568549/5000000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 294
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t465 : ((26034019451/625000000000 : ℚ) : ℝ) ≤ stT301 465 := by
  have hc : ((112279/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26034019451/625000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((112279/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c466 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((226153/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1376809/5000000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 294
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t466 : ((104740179823/5000000000000 : ℚ) : ℝ) ≤ stT301 466 := by
  have hc : ((226103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104740179823/5000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((226103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c467 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-174969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4366677/10000000) (δ := 15191/1000000000) (ψ := 1041953/1000000) 301 294
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t467 : ((-16202460881/2000000000000 : ℚ) : ℝ) ≤ stT301 467 := by
  have hc : ((-175069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16202460881/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-175069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c468 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-14619/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239051/400000) (δ := 1889/125000000) (ψ := 1041953/1000000) 301 294
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t468 : ((-6758571871/200000000000 : ℚ) : ℝ) ≤ stT301 468 := by
  have hc : ((-14621/20000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6758571871/200000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-14621/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c469 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-994109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3791243/5000000) (δ := 15091/1000000000) (ψ := 1041953/1000000) 301 294
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t469 : ((-229541979711/5000000000000 : ℚ) : ℝ) ≤ stT301 469 := by
  have hc : ((-994209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229541979711/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-994209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c470 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-43077/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6522727/10000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 295
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t470 : ((-4968065453/125000000000 : ℚ) : ℝ) ≤ stT301 470 := by
  have hc : ((-21541/25000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4968065453/125000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-21541/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c471 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-194041/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1230841/2500000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 295
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t471 : ((-11179059327/625000000000 : ℚ) : ℝ) ≤ stT301 471 := by
  have hc : ((-194091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11179059327/625000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-194091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c472 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((237549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3327387/10000000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 295
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t472 : ((109294687863/10000000000000 : ℚ) : ℝ) ≤ stT301 472 := by
  have hc : ((237449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109294687863/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((237449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c473 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((384373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -433699/2500000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 295
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t473 : ((883558577/25000000000 : ℚ) : ℝ) ≤ stT301 473 := by
  have hc : ((384323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((883558577/25000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((384323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c474 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((499153/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36379/2500000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 295
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t474 : ((45849098889/1000000000000 : ℚ) : ℝ) ≤ stT301 474 := by
  have hc : ((499103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45849098889/1000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((499103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c475 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((419283/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720189/5000000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 295
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t475 : ((192357096623/5000000000000 : ℚ) : ℝ) ≤ stT301 475 := by
  have hc : ((419233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192357096623/5000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((419233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c476 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((35381/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1511443/5000000) (δ := 15219/1000000000) (ψ := 1041953/1000000) 301 295
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t476 : ((16212262479/1000000000000 : ℚ) : ℝ) ≤ stT301 476 := by
  have hc : ((35371/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16212262479/1000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((35371/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c477 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-266767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2301041/5000000) (δ := 3771/250000000) (ψ := 1041953/1000000) 301 295
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t477 : ((-122190126423/10000000000000 : ℚ) : ℝ) ≤ stT301 477 := by
  have hc : ((-266867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122190126423/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-266867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c478 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-195897/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6178043/10000000) (δ := 15119/1000000000) (ψ := 1041953/1000000) 301 295
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t478 : ((-4480638179/125000000000 : ℚ) : ℝ) ≤ stT301 478 := by
  have hc : ((-97961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4480638179/125000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-97961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c479 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-199829/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7750617/10000000) (δ := 949/62500000) (ψ := 1041953/1000000) 301 295
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t479 : ((-5707087893/125000000000 : ℚ) : ℝ) ≤ stT301 479 := by
  have hc : ((-199849/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5707087893/125000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-199849/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c480 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-832927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1596983/2500000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 296
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t480 : ((-95055877943/2500000000000 : ℚ) : ℝ) ≤ stT301 480 := by
  have hc : ((-833027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95055877943/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-833027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c481 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-350369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301369/625000) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 296
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t481 : ((-159800195709/10000000000000 : ℚ) : ℝ) ≤ stT301 481 := by
  have hc : ((-350469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159800195709/10000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-350469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c482 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((132007/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3259037/10000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 296
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t482 : ((60104698059/5000000000000 : ℚ) : ℝ) ≤ stT301 482 := by
  have hc : ((131957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60104698059/5000000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((131957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c483 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((777703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1699481/10000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 296
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t483 : ((70764205809/2000000000000 : ℚ) : ℝ) ≤ stT301 483 := by
  have hc : ((777603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70764205809/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((777603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c484 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((998363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28617/2000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 296
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t484 : ((90751091067/2000000000000 : ℚ) : ℝ) ≤ stT301 484 := by
  have hc : ((998263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90751091067/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((998263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c485 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((211281/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141/1000) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 296
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t485 : ((2997696233/78125000000 : ℚ) : ℝ) ≤ stT301 485 := by
  have hc : ((26407/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2997696233/78125000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((26407/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c486 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((47153/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2959999/10000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 296
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t486 : ((42766710129/2500000000000 : ℚ) : ℝ) ≤ stT301 486 := by
  have hc : ((94281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42766710129/2500000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((94281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c487 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-57459/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4506763/10000000) (δ := 3769/250000000) (ψ := 1041953/1000000) 301 296
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t487 : ((-814016553/78125000000 : ℚ) : ℝ) ≤ stT301 487 := by
  have hc : ((-14371/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-814016553/78125000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-14371/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c488 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-750851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3025183/5000000) (δ := 1897/125000000) (ψ := 1041953/1000000) 301 296
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t488 : ((-339939747729/10000000000000 : ℚ) : ℝ) ≤ stT301 488 := by
  have hc : ((-750951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339939747729/10000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-750951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c489 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-994461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3795367/5000000) (δ := 15127/1000000000) (ψ := 1041953/1000000) 301 296
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t489 : ((-56219549647/1250000000000 : ℚ) : ℝ) ≤ stT301 489 := by
  have hc : ((-994561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56219549647/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-994561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c490 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-872933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6579947/10000000) (δ := 7567/500000000) (ψ := 1041953/1000000) 301 297
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t490 : ((-197198074941/5000000000000 : ℚ) : ℝ) ≤ stT301 490 := by
  have hc : ((-873033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197198074941/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-873033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c491 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-108179/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20183/40000) (δ := 7567/500000000) (ψ := 1041953/1000000) 301 297
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t491 : ((-6103976997/312500000000 : ℚ) : ℝ) ≤ stT301 491 := by
  have hc : ((-27051/62500 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6103976997/312500000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-27051/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c492 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((41041/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1757357/5000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 297
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t492 : ((1155712959/156250000000 : ℚ) : ℝ) ≤ stT301 492 := by
  have hc : ((5127/31250 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1155712959/156250000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((5127/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c493 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((350237/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -993419/5000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 297
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t493 : ((157716170499/5000000000000 : ℚ) : ℝ) ≤ stT301 493 := by
  have hc : ((350187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157716170499/5000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((350187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c494 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((39319/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115493/2500000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 297
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t494 : ((3537728823/80000000000 : ℚ) : ℝ) ≤ stT301 494 := by
  have hc : ((7863/8000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3537728823/80000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((7863/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c495 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((455747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529867/5000000) (δ := 7567/500000000) (ψ := 1041953/1000000) 301 297
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t495 : ((102410153901/2500000000000 : ℚ) : ℝ) ≤ stT301 495 := by
  have hc : ((455697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102410153901/2500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((455697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c496 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((256821/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2578429/10000000) (δ := 15169/1000000000) (ψ := 1041953/1000000) 301 297
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t496 : ((115293517023/5000000000000 : ℚ) : ℝ) ≤ stT301 496 := by
  have hc : ((256771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115293517023/5000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((256771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c497 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-6677/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102351/250000) (δ := 7617/500000000) (ψ := 1041953/1000000) 301 297
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t497 : ((-1499767047/500000000000 : ℚ) : ℝ) ≤ stT301 497 := by
  have hc : ((-6687/100000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1499767047/500000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-6687/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c498 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-622419/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1121313/2000000) (δ := 7617/500000000) (ψ := 1041953/1000000) 301 297
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t498 : ((-278957611609/10000000000000 : ℚ) : ℝ) ≤ stT301 498 := by
  have hc : ((-622519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278957611609/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-622519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c499 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-191351/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88951/125000) (δ := 7617/500000000) (ψ := 1041953/1000000) 301 297
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t499 : ((-42834762301/1000000000000 : ℚ) : ℝ) ≤ stT301 499 := by
  have hc : ((-191371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42834762301/1000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-191371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_c500 :
    |Real.cos (((301 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-953111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7085379/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 298
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st301_t500 : ((-213144652077/5000000000000 : ℚ) : ℝ) ≤ stT301 500 := by
  have hc : ((-953211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((301 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st301_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213144652077/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-953211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st301_p1 : ((100887/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT301 (i+1) := by
  rw [Finset.sum_range_one]
  exact st301_t1

theorem st301_p2 : ((11894495653719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT301 (i+1))
      = (∑ i ∈ Finset.range 1, stT301 (i+1)) + stT301 2 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 1
    simpa using h
  have hprev := st301_p1
  have hstep := st301_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p3 : ((6268390185309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT301 (i+1))
      = (∑ i ∈ Finset.range 2, stT301 (i+1)) + stT301 3 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 2
    simpa using h
  have hprev := st301_p2
  have hstep := st301_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p4 : ((6409775185309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT301 (i+1))
      = (∑ i ∈ Finset.range 3, stT301 (i+1)) + stT301 4 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 3
    simpa using h
  have hprev := st301_p3
  have hstep := st301_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p5 : ((10517207576059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT301 (i+1))
      = (∑ i ∈ Finset.range 4, stT301 (i+1)) + stT301 5 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 4
    simpa using h
  have hprev := st301_p4
  have hstep := st301_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p6 : ((8539881429907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT301 (i+1))
      = (∑ i ∈ Finset.range 5, stT301 (i+1)) + stT301 6 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 5
    simpa using h
  have hprev := st301_p5
  have hstep := st301_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p7 : ((12101810376219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT301 (i+1))
      = (∑ i ∈ Finset.range 6, stT301 (i+1)) + stT301 7 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 6
    simpa using h
  have hprev := st301_p6
  have hstep := st301_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p8 : ((8731212572853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT301 (i+1))
      = (∑ i ∈ Finset.range 7, stT301 (i+1)) + stT301 8 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 7
    simpa using h
  have hprev := st301_p7
  have hstep := st301_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p9 : ((11504052295569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT301 (i+1))
      = (∑ i ∈ Finset.range 8, stT301 (i+1)) + stT301 9 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 8
    simpa using h
  have hprev := st301_p8
  have hstep := st301_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p10 : ((3376126390873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT301 (i+1))
      = (∑ i ∈ Finset.range 9, stT301 (i+1)) + stT301 10 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 9
    simpa using h
  have hprev := st301_p9
  have hstep := st301_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p11 : ((3174270538801/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT301 (i+1))
      = (∑ i ∈ Finset.range 10, stT301 (i+1)) + stT301 11 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 10
    simpa using h
  have hprev := st301_p10
  have hstep := st301_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p12 : ((7370338348313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT301 (i+1))
      = (∑ i ∈ Finset.range 11, stT301 (i+1)) + stT301 12 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 11
    simpa using h
  have hprev := st301_p11
  have hstep := st301_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p13 : ((14045640119527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT301 (i+1))
      = (∑ i ∈ Finset.range 12, stT301 (i+1)) + stT301 13 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 12
    simpa using h
  have hprev := st301_p12
  have hstep := st301_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p14 : ((2775867889643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT301 (i+1))
      = (∑ i ∈ Finset.range 13, stT301 (i+1)) + stT301 14 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 13
    simpa using h
  have hprev := st301_p13
  have hstep := st301_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p15 : ((11509724207443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT301 (i+1))
      = (∑ i ∈ Finset.range 14, stT301 (i+1)) + stT301 15 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 14
    simpa using h
  have hprev := st301_p14
  have hstep := st301_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p16 : ((10127748654653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT301 (i+1))
      = (∑ i ∈ Finset.range 15, stT301 (i+1)) + stT301 16 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 15
    simpa using h
  have hprev := st301_p15
  have hstep := st301_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p17 : ((7878467722139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT301 (i+1))
      = (∑ i ∈ Finset.range 16, stT301 (i+1)) + stT301 17 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 16
    simpa using h
  have hprev := st301_p16
  have hstep := st301_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p18 : ((7160155534797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT301 (i+1))
      = (∑ i ∈ Finset.range 17, stT301 (i+1)) + stT301 18 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 17
    simpa using h
  have hprev := st301_p17
  have hstep := st301_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p19 : ((4461012260907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT301 (i+1))
      = (∑ i ∈ Finset.range 18, stT301 (i+1)) + stT301 19 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 18
    simpa using h
  have hprev := st301_p18
  have hstep := st301_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p20 : ((3823021811283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT301 (i+1))
      = (∑ i ∈ Finset.range 19, stT301 (i+1)) + stT301 20 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 19
    simpa using h
  have hprev := st301_p19
  have hstep := st301_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p21 : ((3383042152587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT301 (i+1))
      = (∑ i ∈ Finset.range 20, stT301 (i+1)) + stT301 21 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 20
    simpa using h
  have hprev := st301_p20
  have hstep := st301_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p22 : ((1716780765921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT301 (i+1))
      = (∑ i ∈ Finset.range 21, stT301 (i+1)) + stT301 22 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 21
    simpa using h
  have hprev := st301_p21
  have hstep := st301_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p23 : ((10596586990461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT301 (i+1))
      = (∑ i ∈ Finset.range 22, stT301 (i+1)) + stT301 23 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 22
    simpa using h
  have hprev := st301_p22
  have hstep := st301_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p24 : ((12379766138277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT301 (i+1))
      = (∑ i ∈ Finset.range 23, stT301 (i+1)) + stT301 24 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 23
    simpa using h
  have hprev := st301_p23
  have hstep := st301_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p25 : ((14327290138277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT301 (i+1))
      = (∑ i ∈ Finset.range 24, stT301 (i+1)) + stT301 25 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 24
    simpa using h
  have hprev := st301_p24
  have hstep := st301_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p26 : ((16017410843433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT301 (i+1))
      = (∑ i ∈ Finset.range 25, stT301 (i+1)) + stT301 26 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 25
    simpa using h
  have hprev := st301_p25
  have hstep := st301_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p27 : ((1962035835259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT301 (i+1))
      = (∑ i ∈ Finset.range 26, stT301 (i+1)) + stT301 27 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 26
    simpa using h
  have hprev := st301_p26
  have hstep := st301_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p28 : ((1731296006251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT301 (i+1))
      = (∑ i ∈ Finset.range 27, stT301 (i+1)) + stT301 28 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 27
    simpa using h
  have hprev := st301_p27
  have hstep := st301_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p29 : ((14973295383403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT301 (i+1))
      = (∑ i ∈ Finset.range 28, stT301 (i+1)) + stT301 29 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 28
    simpa using h
  have hprev := st301_p28
  have hstep := st301_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p30 : ((7604932886739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT301 (i+1))
      = (∑ i ∈ Finset.range 29, stT301 (i+1)) + stT301 30 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 29
    simpa using h
  have hprev := st301_p29
  have hstep := st301_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p31 : ((7116447507981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT301 (i+1))
      = (∑ i ∈ Finset.range 30, stT301 (i+1)) + stT301 31 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 30
    simpa using h
  have hprev := st301_p30
  have hstep := st301_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p32 : ((7690223692963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT301 (i+1))
      = (∑ i ∈ Finset.range 31, stT301 (i+1)) + stT301 32 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 31
    simpa using h
  have hprev := st301_p31
  have hstep := st301_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p33 : ((1447919839127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT301 (i+1))
      = (∑ i ∈ Finset.range 32, stT301 (i+1)) + stT301 33 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 32
    simpa using h
  have hprev := st301_p32
  have hstep := st301_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p34 : ((2931771700977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT301 (i+1))
      = (∑ i ∈ Finset.range 33, stT301 (i+1)) + stT301 34 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 33
    simpa using h
  have hprev := st301_p33
  have hstep := st301_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p35 : ((3121081126053/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT301 (i+1))
      = (∑ i ∈ Finset.range 34, stT301 (i+1)) + stT301 35 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 34
    simpa using h
  have hprev := st301_p34
  have hstep := st301_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p36 : ((557574878549/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT301 (i+1))
      = (∑ i ∈ Finset.range 35, stT301 (i+1)) + stT301 36 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 35
    simpa using h
  have hprev := st301_p35
  have hstep := st301_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p37 : ((2923138519687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT301 (i+1))
      = (∑ i ∈ Finset.range 36, stT301 (i+1)) + stT301 37 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 36
    simpa using h
  have hprev := st301_p36
  have hstep := st301_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p38 : ((15956929400351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT301 (i+1))
      = (∑ i ∈ Finset.range 37, stT301 (i+1)) + stT301 38 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 37
    simpa using h
  have hprev := st301_p37
  have hstep := st301_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p39 : ((15103643052037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT301 (i+1))
      = (∑ i ∈ Finset.range 38, stT301 (i+1)) + stT301 39 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 38
    simpa using h
  have hprev := st301_p38
  have hstep := st301_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p40 : ((13606921063247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT301 (i+1))
      = (∑ i ∈ Finset.range 39, stT301 (i+1)) + stT301 40 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 39
    simpa using h
  have hprev := st301_p39
  have hstep := st301_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p41 : ((13461802806549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT301 (i+1))
      = (∑ i ∈ Finset.range 40, stT301 (i+1)) + stT301 41 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 40
    simpa using h
  have hprev := st301_p40
  have hstep := st301_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p42 : ((14648203847457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT301 (i+1))
      = (∑ i ∈ Finset.range 41, stT301 (i+1)) + stT301 42 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 41
    simpa using h
  have hprev := st301_p41
  have hstep := st301_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p43 : ((16164487283047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT301 (i+1))
      = (∑ i ∈ Finset.range 42, stT301 (i+1)) + stT301 43 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 42
    simpa using h
  have hprev := st301_p42
  have hstep := st301_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p44 : ((17274981676211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT301 (i+1))
      = (∑ i ∈ Finset.range 43, stT301 (i+1)) + stT301 44 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 43
    simpa using h
  have hprev := st301_p43
  have hstep := st301_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p45 : ((2222737430309/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT301 (i+1))
      = (∑ i ∈ Finset.range 44, stT301 (i+1)) + stT301 45 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 44
    simpa using h
  have hprev := st301_p44
  have hstep := st301_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p46 : ((8901649579919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT301 (i+1))
      = (∑ i ∈ Finset.range 45, stT301 (i+1)) + stT301 46 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 45
    simpa using h
  have hprev := st301_p45
  have hstep := st301_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p47 : ((8774166487219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT301 (i+1))
      = (∑ i ∈ Finset.range 46, stT301 (i+1)) + stT301 47 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 46
    simpa using h
  have hprev := st301_p46
  have hstep := st301_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p48 : ((8609927618931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT301 (i+1))
      = (∑ i ∈ Finset.range 47, stT301 (i+1)) + stT301 48 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 47
    simpa using h
  have hprev := st301_p47
  have hstep := st301_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p49 : ((1700244657947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT301 (i+1))
      = (∑ i ∈ Finset.range 48, stT301 (i+1)) + stT301 49 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 48
    simpa using h
  have hprev := st301_p48
  have hstep := st301_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p50 : ((17072228091529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT301 (i+1))
      = (∑ i ∈ Finset.range 49, stT301 (i+1)) + stT301 50 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 49
    simpa using h
  have hprev := st301_p49
  have hstep := st301_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p51 : ((17581147255009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT301 (i+1))
      = (∑ i ∈ Finset.range 50, stT301 (i+1)) + stT301 51 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 50
    simpa using h
  have hprev := st301_p50
  have hstep := st301_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p52 : ((18585799093759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT301 (i+1))
      = (∑ i ∈ Finset.range 51, stT301 (i+1)) + stT301 52 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 51
    simpa using h
  have hprev := st301_p51
  have hstep := st301_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p53 : ((2491110495533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT301 (i+1))
      = (∑ i ∈ Finset.range 52, stT301 (i+1)) + stT301 53 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 52
    simpa using h
  have hprev := st301_p52
  have hstep := st301_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p54 : ((2644546461437/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT301 (i+1))
      = (∑ i ∈ Finset.range 53, stT301 (i+1)) + stT301 54 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 53
    simpa using h
  have hprev := st301_p53
  have hstep := st301_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p55 : ((10818485379937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT301 (i+1))
      = (∑ i ∈ Finset.range 54, stT301 (i+1)) + stT301 55 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 54
    simpa using h
  have hprev := st301_p54
  have hstep := st301_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p56 : ((4200392336479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT301 (i+1))
      = (∑ i ∈ Finset.range 55, stT301 (i+1)) + stT301 56 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 55
    simpa using h
  have hprev := st301_p55
  have hstep := st301_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p57 : ((246085493617/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT301 (i+1))
      = (∑ i ∈ Finset.range 56, stT301 (i+1)) + stT301 57 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 56
    simpa using h
  have hprev := st301_p56
  have hstep := st301_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p58 : ((1889975418867/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT301 (i+1))
      = (∑ i ∈ Finset.range 57, stT301 (i+1)) + stT301 58 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 57
    simpa using h
  have hprev := st301_p57
  have hstep := st301_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p59 : ((975909526017/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT301 (i+1))
      = (∑ i ∈ Finset.range 58, stT301 (i+1)) + stT301 59 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 58
    simpa using h
  have hprev := st301_p58
  have hstep := st301_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p60 : ((2079483512203/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT301 (i+1))
      = (∑ i ∈ Finset.range 59, stT301 (i+1)) + stT301 60 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 59
    simpa using h
  have hprev := st301_p59
  have hstep := st301_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p61 : ((10470410060327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT301 (i+1))
      = (∑ i ∈ Finset.range 60, stT301 (i+1)) + stT301 61 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 60
    simpa using h
  have hprev := st301_p60
  have hstep := st301_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p62 : ((9863032873829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT301 (i+1))
      = (∑ i ∈ Finset.range 61, stT301 (i+1)) + stT301 62 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 61
    simpa using h
  have hprev := st301_p61
  have hstep := st301_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p63 : ((480879479597/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT301 (i+1))
      = (∑ i ∈ Finset.range 62, stT301 (i+1)) + stT301 63 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 62
    simpa using h
  have hprev := st301_p62
  have hstep := st301_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p64 : ((509307948347/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT301 (i+1))
      = (∑ i ∈ Finset.range 63, stT301 (i+1)) + stT301 64 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 63
    simpa using h
  have hprev := st301_p63
  have hstep := st301_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p65 : ((20834963643839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT301 (i+1))
      = (∑ i ∈ Finset.range 64, stT301 (i+1)) + stT301 65 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 64
    simpa using h
  have hprev := st301_p64
  have hstep := st301_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p66 : ((2455880716963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT301 (i+1))
      = (∑ i ∈ Finset.range 65, stT301 (i+1)) + stT301 66 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 65
    simpa using h
  have hprev := st301_p65
  have hstep := st301_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p67 : ((4887477802411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT301 (i+1))
      = (∑ i ∈ Finset.range 66, stT301 (i+1)) + stT301 67 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 66
    simpa using h
  have hprev := st301_p66
  have hstep := st301_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p68 : ((324128923327/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT301 (i+1))
      = (∑ i ∈ Finset.range 67, stT301 (i+1)) + stT301 68 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 67
    simpa using h
  have hprev := st301_p67
  have hstep := st301_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p69 : ((4035151273787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT301 (i+1))
      = (∑ i ∈ Finset.range 68, stT301 (i+1)) + stT301 69 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 68
    simpa using h
  have hprev := st301_p68
  have hstep := st301_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p70 : ((3881550004539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT301 (i+1))
      = (∑ i ∈ Finset.range 69, stT301 (i+1)) + stT301 70 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 69
    simpa using h
  have hprev := st301_p69
  have hstep := st301_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p71 : ((20556072197609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT301 (i+1))
      = (∑ i ∈ Finset.range 70, stT301 (i+1)) + stT301 71 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 70
    simpa using h
  have hprev := st301_p70
  have hstep := st301_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p72 : ((20267088091577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT301 (i+1))
      = (∑ i ∈ Finset.range 71, stT301 (i+1)) + stT301 72 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 71
    simpa using h
  have hprev := st301_p71
  have hstep := st301_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p73 : ((19458482041901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT301 (i+1))
      = (∑ i ∈ Finset.range 72, stT301 (i+1)) + stT301 73 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 72
    simpa using h
  have hprev := st301_p72
  have hstep := st301_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p74 : ((20608566047741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT301 (i+1))
      = (∑ i ∈ Finset.range 73, stT301 (i+1)) + stT301 74 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 73
    simpa using h
  have hprev := st301_p73
  have hstep := st301_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p75 : ((500702994859/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT301 (i+1))
      = (∑ i ∈ Finset.range 74, stT301 (i+1)) + stT301 75 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 74
    simpa using h
  have hprev := st301_p74
  have hstep := st301_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p76 : ((9834332118223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT301 (i+1))
      = (∑ i ∈ Finset.range 75, stT301 (i+1)) + stT301 76 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 75
    simpa using h
  have hprev := st301_p75
  have hstep := st301_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p77 : ((20690173109901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT301 (i+1))
      = (∑ i ∈ Finset.range 76, stT301 (i+1)) + stT301 77 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 76
    simpa using h
  have hprev := st301_p76
  have hstep := st301_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p78 : ((19602908821791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT301 (i+1))
      = (∑ i ∈ Finset.range 77, stT301 (i+1)) + stT301 78 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 77
    simpa using h
  have hprev := st301_p77
  have hstep := st301_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p79 : ((20233115053971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT301 (i+1))
      = (∑ i ∈ Finset.range 78, stT301 (i+1)) + stT301 79 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 78
    simpa using h
  have hprev := st301_p78
  have hstep := st301_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p80 : ((20288826638361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT301 (i+1))
      = (∑ i ∈ Finset.range 79, stT301 (i+1)) + stT301 80 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 79
    simpa using h
  have hprev := st301_p79
  have hstep := st301_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p81 : ((19618471657633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT301 (i+1))
      = (∑ i ∈ Finset.range 80, stT301 (i+1)) + stT301 81 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 80
    simpa using h
  have hprev := st301_p80
  have hstep := st301_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p82 : ((10323660541739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT301 (i+1))
      = (∑ i ∈ Finset.range 81, stT301 (i+1)) + stT301 82 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 81
    simpa using h
  have hprev := st301_p81
  have hstep := st301_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p83 : ((19559612850271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT301 (i+1))
      = (∑ i ∈ Finset.range 82, stT301 (i+1)) + stT301 83 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 82
    simpa using h
  have hprev := st301_p82
  have hstep := st301_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p84 : ((10230434365303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT301 (i+1))
      = (∑ i ∈ Finset.range 83, stT301 (i+1)) + stT301 84 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 83
    simpa using h
  have hprev := st301_p83
  have hstep := st301_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p85 : ((19892346776003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT301 (i+1))
      = (∑ i ∈ Finset.range 84, stT301 (i+1)) + stT301 85 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 84
    simpa using h
  have hprev := st301_p84
  have hstep := st301_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p86 : ((20077538654983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT301 (i+1))
      = (∑ i ∈ Finset.range 85, stT301 (i+1)) + stT301 86 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 85
    simpa using h
  have hprev := st301_p85
  have hstep := st301_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p87 : ((4050820098363/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT301 (i+1))
      = (∑ i ∈ Finset.range 86, stT301 (i+1)) + stT301 87 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 86
    simpa using h
  have hprev := st301_p86
  have hstep := st301_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p88 : ((19776938979347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT301 (i+1))
      = (∑ i ∈ Finset.range 87, stT301 (i+1)) + stT301 88 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 87
    simpa using h
  have hprev := st301_p87
  have hstep := st301_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p89 : ((2559824836689/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT301 (i+1))
      = (∑ i ∈ Finset.range 88, stT301 (i+1)) + stT301 89 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 88
    simpa using h
  have hprev := st301_p88
  have hstep := st301_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p90 : ((1916414399/976562500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT301 (i+1))
      = (∑ i ∈ Finset.range 89, stT301 (i+1)) + stT301 90 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 89
    simpa using h
  have hprev := st301_p89
  have hstep := st301_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p91 : ((20571847493/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT301 (i+1))
      = (∑ i ∈ Finset.range 90, stT301 (i+1)) + stT301 91 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 90
    simpa using h
  have hprev := st301_p90
  have hstep := st301_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p92 : ((19573668293913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT301 (i+1))
      = (∑ i ∈ Finset.range 91, stT301 (i+1)) + stT301 92 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 91
    simpa using h
  have hprev := st301_p91
  have hstep := st301_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p93 : ((5148406694469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT301 (i+1))
      = (∑ i ∈ Finset.range 92, stT301 (i+1)) + stT301 93 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 92
    simpa using h
  have hprev := st301_p92
  have hstep := st301_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p94 : ((4891893074491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT301 (i+1))
      = (∑ i ∈ Finset.range 93, stT301 (i+1)) + stT301 94 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 93
    simpa using h
  have hprev := st301_p93
  have hstep := st301_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p95 : ((10295818424497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT301 (i+1))
      = (∑ i ∈ Finset.range 94, stT301 (i+1)) + stT301 95 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 94
    simpa using h
  have hprev := st301_p94
  have hstep := st301_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p96 : ((9786073348531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT301 (i+1))
      = (∑ i ∈ Finset.range 95, stT301 (i+1)) + stT301 96 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 95
    simpa using h
  have hprev := st301_p95
  have hstep := st301_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p97 : ((10292396953697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT301 (i+1))
      = (∑ i ∈ Finset.range 96, stT301 (i+1)) + stT301 97 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 96
    simpa using h
  have hprev := st301_p96
  have hstep := st301_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p98 : ((4895634570887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT301 (i+1))
      = (∑ i ∈ Finset.range 97, stT301 (i+1)) + stT301 98 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 97
    simpa using h
  have hprev := st301_p97
  have hstep := st301_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p99 : ((20565049389267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT301 (i+1))
      = (∑ i ∈ Finset.range 98, stT301 (i+1)) + stT301 99 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 98
    simpa using h
  have hprev := st301_p98
  have hstep := st301_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p100 : ((19618292389267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT301 (i+1))
      = (∑ i ∈ Finset.range 99, stT301 (i+1)) + stT301 100 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 99
    simpa using h
  have hprev := st301_p99
  have hstep := st301_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p101 : ((20503244465809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT301 (i+1))
      = (∑ i ∈ Finset.range 100, stT301 (i+1)) + stT301 101 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 100
    simpa using h
  have hprev := st301_p100
  have hstep := st301_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p102 : ((3943061294133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT301 (i+1))
      = (∑ i ∈ Finset.range 101, stT301 (i+1)) + stT301 102 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 101
    simpa using h
  have hprev := st301_p101
  have hstep := st301_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p103 : ((1272580941273/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT301 (i+1))
      = (∑ i ∈ Finset.range 102, stT301 (i+1)) + stT301 103 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 102
    simpa using h
  have hprev := st301_p102
  have hstep := st301_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p104 : ((1990685656289/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT301 (i+1))
      = (∑ i ∈ Finset.range 103, stT301 (i+1)) + stT301 104 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 103
    simpa using h
  have hprev := st301_p103
  have hstep := st301_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p105 : ((2012028686879/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT301 (i+1))
      = (∑ i ∈ Finset.range 104, stT301 (i+1)) + stT301 105 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 104
    simpa using h
  have hprev := st301_p104
  have hstep := st301_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p106 : ((4037221587877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT301 (i+1))
      = (∑ i ∈ Finset.range 105, stT301 (i+1)) + stT301 106 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 105
    simpa using h
  have hprev := st301_p105
  have hstep := st301_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p107 : ((4956143600821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT301 (i+1))
      = (∑ i ∈ Finset.range 106, stT301 (i+1)) + stT301 107 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 106
    simpa using h
  have hprev := st301_p106
  have hstep := st301_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p108 : ((2557800226973/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT301 (i+1))
      = (∑ i ∈ Finset.range 107, stT301 (i+1)) + stT301 108 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 107
    simpa using h
  have hprev := st301_p107
  have hstep := st301_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p109 : ((9806060773499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT301 (i+1))
      = (∑ i ∈ Finset.range 108, stT301 (i+1)) + stT301 109 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 108
    simpa using h
  have hprev := st301_p108
  have hstep := st301_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p110 : ((10280984963009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT301 (i+1))
      = (∑ i ∈ Finset.range 109, stT301 (i+1)) + stT301 110 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 109
    simpa using h
  have hprev := st301_p109
  have hstep := st301_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p111 : ((122902723003/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT301 (i+1))
      = (∑ i ∈ Finset.range 110, stT301 (i+1)) + stT301 111 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 110
    simpa using h
  have hprev := st301_p110
  have hstep := st301_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p112 : ((813611141947/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT301 (i+1))
      = (∑ i ∈ Finset.range 111, stT301 (i+1)) + stT301 112 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 111
    simpa using h
  have hprev := st301_p111
  have hstep := st301_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p113 : ((10017179450819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT301 (i+1))
      = (∑ i ∈ Finset.range 112, stT301 (i+1)) + stT301 113 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 112
    simpa using h
  have hprev := st301_p112
  have hstep := st301_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p114 : ((4971612139397/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT301 (i+1))
      = (∑ i ∈ Finset.range 113, stT301 (i+1)) + stT301 114 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 113
    simpa using h
  have hprev := st301_p113
  have hstep := st301_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p115 : ((5116582708127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT301 (i+1))
      = (∑ i ∈ Finset.range 114, stT301 (i+1)) + stT301 115 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 114
    simpa using h
  have hprev := st301_p114
  have hstep := st301_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p116 : ((19598603154141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT301 (i+1))
      = (∑ i ∈ Finset.range 115, stT301 (i+1)) + stT301 116 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 115
    simpa using h
  have hprev := st301_p115
  have hstep := st301_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p117 : ((20505695743641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT301 (i+1))
      = (∑ i ∈ Finset.range 116, stT301 (i+1)) + stT301 117 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 116
    simpa using h
  have hprev := st301_p116
  have hstep := st301_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p118 : ((4961774724429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT301 (i+1))
      = (∑ i ∈ Finset.range 117, stT301 (i+1)) + stT301 118 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 117
    simpa using h
  have hprev := st301_p117
  have hstep := st301_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p119 : ((625785681771/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT301 (i+1))
      = (∑ i ∈ Finset.range 118, stT301 (i+1)) + stT301 119 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 118
    simpa using h
  have hprev := st301_p118
  have hstep := st301_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p120 : ((10201624003161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT301 (i+1))
      = (∑ i ∈ Finset.range 119, stT301 (i+1)) + stT301 120 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 119
    simpa using h
  have hprev := st301_p119
  have hstep := st301_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p121 : ((19605343381077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT301 (i+1))
      = (∑ i ∈ Finset.range 120, stT301 (i+1)) + stT301 121 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 120
    simpa using h
  have hprev := st301_p120
  have hstep := st301_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p122 : ((5124606614057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT301 (i+1))
      = (∑ i ∈ Finset.range 121, stT301 (i+1)) + stT301 122 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 121
    simpa using h
  have hprev := st301_p121
  have hstep := st301_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p123 : ((4975588514827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT301 (i+1))
      = (∑ i ∈ Finset.range 122, stT301 (i+1)) + stT301 123 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 122
    simpa using h
  have hprev := st301_p122
  have hstep := st301_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p124 : ((9959116926533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT301 (i+1))
      = (∑ i ∈ Finset.range 123, stT301 (i+1)) + stT301 124 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 123
    simpa using h
  have hprev := st301_p123
  have hstep := st301_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p125 : ((10249261889917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT301 (i+1))
      = (∑ i ∈ Finset.range 124, stT301 (i+1)) + stT301 125 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 124
    simpa using h
  have hprev := st301_p124
  have hstep := st301_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p126 : ((153235413871/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT301 (i+1))
      = (∑ i ∈ Finset.range 125, stT301 (i+1)) + stT301 126 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 125
    simpa using h
  have hprev := st301_p125
  have hstep := st301_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p127 : ((254068102417/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT301 (i+1))
      = (∑ i ∈ Finset.range 126, stT301 (i+1)) + stT301 127 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 126
    simpa using h
  have hprev := st301_p126
  have hstep := st301_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p128 : ((504845725673/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT301 (i+1))
      = (∑ i ∈ Finset.range 127, stT301 (i+1)) + stT301 128 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 127
    simpa using h
  have hprev := st301_p127
  have hstep := st301_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p129 : ((4915263509901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT301 (i+1))
      = (∑ i ∈ Finset.range 128, stT301 (i+1)) + stT301 129 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 128
    simpa using h
  have hprev := st301_p128
  have hstep := st301_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p130 : ((5133327317499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT301 (i+1))
      = (∑ i ∈ Finset.range 129, stT301 (i+1)) + stT301 130 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 129
    simpa using h
  have hprev := st301_p129
  have hstep := st301_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p131 : ((9941464255113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT301 (i+1))
      = (∑ i ∈ Finset.range 130, stT301 (i+1)) + stT301 131 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 130
    simpa using h
  have hprev := st301_p130
  have hstep := st301_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p132 : ((19871412393367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT301 (i+1))
      = (∑ i ∈ Finset.range 131, stT301 (i+1)) + stT301 132 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 131
    simpa using h
  have hprev := st301_p131
  have hstep := st301_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p133 : ((20541304388189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT301 (i+1))
      = (∑ i ∈ Finset.range 132, stT301 (i+1)) + stT301 133 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 132
    simpa using h
  have hprev := st301_p132
  have hstep := st301_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p134 : ((9847209958299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT301 (i+1))
      = (∑ i ∈ Finset.range 133, stT301 (i+1)) + stT301 134 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 133
    simpa using h
  have hprev := st301_p133
  have hstep := st301_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p135 : ((1255161101121/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT301 (i+1))
      = (∑ i ∈ Finset.range 134, stT301 (i+1)) + stT301 135 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 134
    simpa using h
  have hprev := st301_p134
  have hstep := st301_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p136 : ((2557144909783/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT301 (i+1))
      = (∑ i ∈ Finset.range 135, stT301 (i+1)) + stT301 136 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 135
    simpa using h
  have hprev := st301_p135
  have hstep := st301_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p137 : ((2452106719831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT301 (i+1))
      = (∑ i ∈ Finset.range 136, stT301 (i+1)) + stT301 137 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 136
    simpa using h
  have hprev := st301_p136
  have hstep := st301_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p138 : ((2528461829263/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT301 (i+1))
      = (∑ i ∈ Finset.range 137, stT301 (i+1)) + stT301 138 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 137
    simpa using h
  have hprev := st301_p137
  have hstep := st301_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p139 : ((2546160968259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT301 (i+1))
      = (∑ i ∈ Finset.range 138, stT301 (i+1)) + stT301 139 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 138
    simpa using h
  have hprev := st301_p138
  have hstep := st301_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p140 : ((4899297831223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT301 (i+1))
      = (∑ i ∈ Finset.range 139, stT301 (i+1)) + stT301 140 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 139
    simpa using h
  have hprev := st301_p139
  have hstep := st301_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p141 : ((20301462836719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT301 (i+1))
      = (∑ i ∈ Finset.range 140, stT301 (i+1)) + stT301 141 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 140
    simpa using h
  have hprev := st301_p140
  have hstep := st301_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p142 : ((10160643404741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT301 (i+1))
      = (∑ i ∈ Finset.range 141, stT301 (i+1)) + stT301 142 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 141
    simpa using h
  have hprev := st301_p141
  have hstep := st301_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p143 : ((1224660827821/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT301 (i+1))
      = (∑ i ∈ Finset.range 142, stT301 (i+1)) + stT301 143 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 142
    simpa using h
  have hprev := st301_p142
  have hstep := st301_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p144 : ((1015753147847/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT301 (i+1))
      = (∑ i ∈ Finset.range 143, stT301 (i+1)) + stT301 144 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 143
    simpa using h
  have hprev := st301_p143
  have hstep := st301_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p145 : ((10163300227181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT301 (i+1))
      = (∑ i ∈ Finset.range 144, stT301 (i+1)) + stT301 145 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 144
    simpa using h
  have hprev := st301_p144
  have hstep := st301_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p146 : ((1224621967749/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT301 (i+1))
      = (∑ i ∈ Finset.range 145, stT301 (i+1)) + stT301 146 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 145
    simpa using h
  have hprev := st301_p145
  have hstep := st301_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p147 : ((10136586738601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT301 (i+1))
      = (∑ i ∈ Finset.range 146, stT301 (i+1)) + stT301 147 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 146
    simpa using h
  have hprev := st301_p146
  have hstep := st301_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p148 : ((1019110836763/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT301 (i+1))
      = (∑ i ∈ Finset.range 147, stT301 (i+1)) + stT301 148 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 147
    simpa using h
  have hprev := st301_p147
  have hstep := st301_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p149 : ((4901317963159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT301 (i+1))
      = (∑ i ∈ Finset.range 148, stT301 (i+1)) + stT301 149 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 148
    simpa using h
  have hprev := st301_p148
  have hstep := st301_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p150 : ((5042746297179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT301 (i+1))
      = (∑ i ∈ Finset.range 149, stT301 (i+1)) + stT301 150 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 149
    simpa using h
  have hprev := st301_p149
  have hstep := st301_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p151 : ((5117430063303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT301 (i+1))
      = (∑ i ∈ Finset.range 150, stT301 (i+1)) + stT301 151 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 150
    simpa using h
  have hprev := st301_p150
  have hstep := st301_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p152 : ((245739760499/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT301 (i+1))
      = (∑ i ∈ Finset.range 151, stT301 (i+1)) + stT301 152 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 151
    simpa using h
  have hprev := st301_p151
  have hstep := st301_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p153 : ((2500706176517/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT301 (i+1))
      = (∑ i ∈ Finset.range 152, stT301 (i+1)) + stT301 153 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 152
    simpa using h
  have hprev := st301_p152
  have hstep := st301_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p154 : ((10273765834217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT301 (i+1))
      = (∑ i ∈ Finset.range 153, stT301 (i+1)) + stT301 154 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 153
    simpa using h
  have hprev := st301_p153
  have hstep := st301_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p155 : ((9897893412677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT301 (i+1))
      = (∑ i ∈ Finset.range 154, stT301 (i+1)) + stT301 155 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 154
    simpa using h
  have hprev := st301_p154
  have hstep := st301_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p156 : ((9899722875077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT301 (i+1))
      = (∑ i ∈ Finset.range 155, stT301 (i+1)) + stT301 156 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 155
    simpa using h
  have hprev := st301_p155
  have hstep := st301_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p157 : ((10273537578531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT301 (i+1))
      = (∑ i ∈ Finset.range 156, stT301 (i+1)) + stT301 157 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 156
    simpa using h
  have hprev := st301_p156
  have hstep := st301_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p158 : ((10017997984467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT301 (i+1))
      = (∑ i ∈ Finset.range 157, stT301 (i+1)) + stT301 158 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 157
    simpa using h
  have hprev := st301_p157
  have hstep := st301_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p159 : ((9812389736843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT301 (i+1))
      = (∑ i ∈ Finset.range 158, stT301 (i+1)) + stT301 159 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 158
    simpa using h
  have hprev := st301_p158
  have hstep := st301_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p160 : ((10197346243427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT301 (i+1))
      = (∑ i ∈ Finset.range 159, stT301 (i+1)) + stT301 160 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 159
    simpa using h
  have hprev := st301_p159
  have hstep := st301_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p161 : ((5083707287879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT301 (i+1))
      = (∑ i ∈ Finset.range 160, stT301 (i+1)) + stT301 161 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 160
    simpa using h
  have hprev := st301_p160
  have hstep := st301_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p162 : ((19601939726391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT301 (i+1))
      = (∑ i ∈ Finset.range 161, stT301 (i+1)) + stT301 162 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 161
    simpa using h
  have hprev := st301_p161
  have hstep := st301_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p163 : ((20076162143611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT301 (i+1))
      = (∑ i ∈ Finset.range 162, stT301 (i+1)) + stT301 163 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 162
    simpa using h
  have hprev := st301_p162
  have hstep := st301_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p164 : ((20548755951099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT301 (i+1))
      = (∑ i ∈ Finset.range 163, stT301 (i+1)) + stT301 164 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 163
    simpa using h
  have hprev := st301_p163
  have hstep := st301_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p165 : ((19828986915659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT301 (i+1))
      = (∑ i ∈ Finset.range 164, stT301 (i+1)) + stT301 165 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 164
    simpa using h
  have hprev := st301_p164
  have hstep := st301_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p166 : ((9859054932277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT301 (i+1))
      = (∑ i ∈ Finset.range 165, stT301 (i+1)) + stT301 166 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 165
    simpa using h
  have hprev := st301_p165
  have hstep := st301_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p167 : ((10244226878173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT301 (i+1))
      = (∑ i ∈ Finset.range 166, stT301 (i+1)) + stT301 167 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 166
    simpa using h
  have hprev := st301_p166
  have hstep := st301_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p168 : ((2530710448503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT301 (i+1))
      = (∑ i ∈ Finset.range 167, stT301 (i+1)) + stT301 168 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 167
    simpa using h
  have hprev := st301_p167
  have hstep := st301_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p169 : ((1958408800493/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT301 (i+1))
      = (∑ i ∈ Finset.range 168, stT301 (i+1)) + stT301 169 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 168
    simpa using h
  have hprev := st301_p168
  have hstep := st301_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p170 : ((10050750163233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT301 (i+1))
      = (∑ i ∈ Finset.range 169, stT301 (i+1)) + stT301 170 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 169
    simpa using h
  have hprev := st301_p169
  have hstep := st301_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p171 : ((1027770576221/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT301 (i+1))
      = (∑ i ∈ Finset.range 170, stT301 (i+1)) + stT301 171 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 170
    simpa using h
  have hprev := st301_p170
  have hstep := st301_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p172 : ((496729576857/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT301 (i+1))
      = (∑ i ∈ Finset.range 171, stT301 (i+1)) + stT301 172 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 171
    simpa using h
  have hprev := st301_p171
  have hstep := st301_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p173 : ((2457633178223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT301 (i+1))
      = (∑ i ∈ Finset.range 172, stT301 (i+1)) + stT301 173 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 172
    simpa using h
  have hprev := st301_p172
  have hstep := st301_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p174 : ((510356122149/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT301 (i+1))
      = (∑ i ∈ Finset.range 173, stT301 (i+1)) + stT301 174 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 173
    simpa using h
  have hprev := st301_p173
  have hstep := st301_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p175 : ((20383146722829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT301 (i+1))
      = (∑ i ∈ Finset.range 174, stT301 (i+1)) + stT301 175 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 174
    simpa using h
  have hprev := st301_p174
  have hstep := st301_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p176 : ((982110191271/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT301 (i+1))
      = (∑ i ∈ Finset.range 175, stT301 (i+1)) + stT301 176 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 175
    simpa using h
  have hprev := st301_p175
  have hstep := st301_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p177 : ((49696359693/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT301 (i+1))
      = (∑ i ∈ Finset.range 176, stT301 (i+1)) + stT301 177 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 176
    simpa using h
  have hprev := st301_p176
  have hstep := st301_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p178 : ((20555023337347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT301 (i+1))
      = (∑ i ∈ Finset.range 177, stT301 (i+1)) + stT301 178 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 177
    simpa using h
  have hprev := st301_p177
  have hstep := st301_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p179 : ((20157645250767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT301 (i+1))
      = (∑ i ∈ Finset.range 178, stT301 (i+1)) + stT301 179 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 178
    simpa using h
  have hprev := st301_p178
  have hstep := st301_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p180 : ((19571732824863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT301 (i+1))
      = (∑ i ∈ Finset.range 179, stT301 (i+1)) + stT301 180 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 179
    simpa using h
  have hprev := st301_p179
  have hstep := st301_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p181 : ((20085512503543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT301 (i+1))
      = (∑ i ∈ Finset.range 180, stT301 (i+1)) + stT301 181 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 180
    simpa using h
  have hprev := st301_p180
  have hstep := st301_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p182 : ((2571768073199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT301 (i+1))
      = (∑ i ∈ Finset.range 181, stT301 (i+1)) + stT301 182 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 181
    simpa using h
  have hprev := st301_p181
  have hstep := st301_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p183 : ((9990871581561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT301 (i+1))
      = (∑ i ∈ Finset.range 182, stT301 (i+1)) + stT301 183 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 182
    simpa using h
  have hprev := st301_p182
  have hstep := st301_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p184 : ((9791358227631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT301 (i+1))
      = (∑ i ∈ Finset.range 183, stT301 (i+1)) + stT301 184 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 183
    simpa using h
  have hprev := st301_p183
  have hstep := st301_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p185 : ((5055969183471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT301 (i+1))
      = (∑ i ∈ Finset.range 184, stT301 (i+1)) + stT301 185 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 184
    simpa using h
  have hprev := st301_p184
  have hstep := st301_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p186 : ((2568610576763/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT301 (i+1))
      = (∑ i ∈ Finset.range 185, stT301 (i+1)) + stT301 186 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 185
    simpa using h
  have hprev := st301_p185
  have hstep := st301_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p187 : ((19879956293719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT301 (i+1))
      = (∑ i ∈ Finset.range 186, stT301 (i+1)) + stT301 187 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 186
    simpa using h
  have hprev := st301_p186
  have hstep := st301_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p188 : ((9804124955797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT301 (i+1))
      = (∑ i ∈ Finset.range 187, stT301 (i+1)) + stT301 188 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 187
    simpa using h
  have hprev := st301_p187
  have hstep := st301_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p189 : ((10145030673349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT301 (i+1))
      = (∑ i ∈ Finset.range 188, stT301 (i+1)) + stT301 189 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 188
    simpa using h
  have hprev := st301_p188
  have hstep := st301_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p190 : ((2053057260117/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT301 (i+1))
      = (∑ i ∈ Finset.range 189, stT301 (i+1)) + stT301 190 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 189
    simpa using h
  have hprev := st301_p189
  have hstep := st301_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p191 : ((3969134971129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT301 (i+1))
      = (∑ i ∈ Finset.range 190, stT301 (i+1)) + stT301 191 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 190
    simpa using h
  have hprev := st301_p190
  have hstep := st301_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p192 : ((19613279050949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT301 (i+1))
      = (∑ i ∈ Finset.range 191, stT301 (i+1)) + stT301 192 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 191
    simpa using h
  have hprev := st301_p191
  have hstep := st301_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p193 : ((20293027708419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT301 (i+1))
      = (∑ i ∈ Finset.range 192, stT301 (i+1)) + stT301 193 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 192
    simpa using h
  have hprev := st301_p192
  have hstep := st301_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p194 : ((20539239199233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT301 (i+1))
      = (∑ i ∈ Finset.range 193, stT301 (i+1)) + stT301 194 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 193
    simpa using h
  have hprev := st301_p193
  have hstep := st301_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p195 : ((19872392911233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT301 (i+1))
      = (∑ i ∈ Finset.range 194, stT301 (i+1)) + stT301 195 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 194
    simpa using h
  have hprev := st301_p194
  have hstep := st301_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p196 : ((19591188513037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT301 (i+1))
      = (∑ i ∈ Finset.range 195, stT301 (i+1)) + stT301 196 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 195
    simpa using h
  have hprev := st301_p195
  have hstep := st301_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p197 : ((20234657218477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT301 (i+1))
      = (∑ i ∈ Finset.range 196, stT301 (i+1)) + stT301 197 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 196
    simpa using h
  have hprev := st301_p196
  have hstep := st301_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p198 : ((20569201807551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT301 (i+1))
      = (∑ i ∈ Finset.range 197, stT301 (i+1)) + stT301 198 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 197
    simpa using h
  have hprev := st301_p197
  have hstep := st301_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p199 : ((19962824853633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT301 (i+1))
      = (∑ i ∈ Finset.range 198, stT301 (i+1)) + stT301 199 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 198
    simpa using h
  have hprev := st301_p198
  have hstep := st301_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p200 : ((19559588601599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT301 (i+1))
      = (∑ i ∈ Finset.range 199, stT301 (i+1)) + stT301 200 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 199
    simpa using h
  have hprev := st301_p199
  have hstep := st301_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p201 : ((5027410682591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT301 (i+1))
      = (∑ i ∈ Finset.range 200, stT301 (i+1)) + stT301 201 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 200
    simpa using h
  have hprev := st301_p200
  have hstep := st301_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p202 : ((20590844679813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT301 (i+1))
      = (∑ i ∈ Finset.range 201, stT301 (i+1)) + stT301 202 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 201
    simpa using h
  have hprev := st301_p201
  have hstep := st301_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p203 : ((125756662601/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT301 (i+1))
      = (∑ i ∈ Finset.range 202, stT301 (i+1)) + stT301 203 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 202
    simpa using h
  have hprev := st301_p202
  have hstep := st301_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p204 : ((2445005029037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT301 (i+1))
      = (∑ i ∈ Finset.range 203, stT301 (i+1)) + stT301 204 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 203
    simpa using h
  have hprev := st301_p203
  have hstep := st301_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p205 : ((1245037882291/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT301 (i+1))
      = (∑ i ∈ Finset.range 204, stT301 (i+1)) + stT301 205 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 204
    simpa using h
  have hprev := st301_p204
  have hstep := st301_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p206 : ((20551937486679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT301 (i+1))
      = (∑ i ∈ Finset.range 205, stT301 (i+1)) + stT301 206 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 205
    simpa using h
  have hprev := st301_p205
  have hstep := st301_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p207 : ((4066205178543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT301 (i+1))
      = (∑ i ∈ Finset.range 206, stT301 (i+1)) + stT301 207 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 206
    simpa using h
  have hprev := st301_p206
  have hstep := st301_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p208 : ((3930367966511/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT301 (i+1))
      = (∑ i ∈ Finset.range 207, stT301 (i+1)) + stT301 208 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 207
    simpa using h
  have hprev := st301_p207
  have hstep := st301_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p209 : ((19704300114029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT301 (i+1))
      = (∑ i ∈ Finset.range 208, stT301 (i+1)) + stT301 209 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 208
    simpa using h
  have hprev := st301_p208
  have hstep := st301_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p210 : ((10196567364067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT301 (i+1))
      = (∑ i ∈ Finset.range 209, stT301 (i+1)) + stT301 210 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 209
    simpa using h
  have hprev := st301_p209
  have hstep := st301_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p211 : ((10264541367931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT301 (i+1))
      = (∑ i ∈ Finset.range 210, stT301 (i+1)) + stT301 211 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 210
    simpa using h
  have hprev := st301_p210
  have hstep := st301_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p212 : ((3976607062537/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT301 (i+1))
      = (∑ i ∈ Finset.range 211, stT301 (i+1)) + stT301 212 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 211
    simpa using h
  have hprev := st301_p211
  have hstep := st301_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p213 : ((6110613443/3125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT301 (i+1))
      = (∑ i ∈ Finset.range 212, stT301 (i+1)) + stT301 213 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 212
    simpa using h
  have hprev := st301_p212
  have hstep := st301_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p214 : ((1004658606563/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT301 (i+1))
      = (∑ i ∈ Finset.range 213, stT301 (i+1)) + stT301 214 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 213
    simpa using h
  have hprev := st301_p213
  have hstep := st301_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p215 : ((10298028046511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT301 (i+1))
      = (∑ i ∈ Finset.range 214, stT301 (i+1)) + stT301 215 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 214
    simpa using h
  have hprev := st301_p214
  have hstep := st301_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p216 : ((5057570634243/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT301 (i+1))
      = (∑ i ∈ Finset.range 215, stT301 (i+1)) + stT301 216 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 215
    simpa using h
  have hprev := st301_p215
  have hstep := st301_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p217 : ((19601555984477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT301 (i+1))
      = (∑ i ∈ Finset.range 216, stT301 (i+1)) + stT301 217 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 216
    simpa using h
  have hprev := st301_p216
  have hstep := st301_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p218 : ((19736072912897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT301 (i+1))
      = (∑ i ∈ Finset.range 217, stT301 (i+1)) + stT301 218 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 217
    simpa using h
  have hprev := st301_p217
  have hstep := st301_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p219 : ((10205863398623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT301 (i+1))
      = (∑ i ∈ Finset.range 218, stT301 (i+1)) + stT301 219 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 218
    simpa using h
  have hprev := st301_p218
  have hstep := st301_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p220 : ((2054075230507/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT301 (i+1))
      = (∑ i ∈ Finset.range 219, stT301 (i+1)) + stT301 220 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 219
    simpa using h
  have hprev := st301_p219
  have hstep := st301_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p221 : ((9960342512181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT301 (i+1))
      = (∑ i ∈ Finset.range 220, stT301 (i+1)) + stT301 221 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 220
    simpa using h
  have hprev := st301_p220
  have hstep := st301_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p222 : ((9767992942923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT301 (i+1))
      = (∑ i ∈ Finset.range 221, stT301 (i+1)) + stT301 222 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 221
    simpa using h
  have hprev := st301_p221
  have hstep := st301_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p223 : ((499717820167/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT301 (i+1))
      = (∑ i ∈ Finset.range 222, stT301 (i+1)) + stT301 223 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 222
    simpa using h
  have hprev := st301_p222
  have hstep := st301_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p224 : ((20568974956601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT301 (i+1))
      = (∑ i ∈ Finset.range 223, stT301 (i+1)) + stT301 224 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 223
    simpa using h
  have hprev := st301_p223
  have hstep := st301_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p225 : ((5094809215433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT301 (i+1))
      = (∑ i ∈ Finset.range 224, stT301 (i+1)) + stT301 225 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 224
    simpa using h
  have hprev := st301_p224
  have hstep := st301_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p226 : ((1971489597583/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT301 (i+1))
      = (∑ i ∈ Finset.range 225, stT301 (i+1)) + stT301 226 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 225
    simpa using h
  have hprev := st301_p225
  have hstep := st301_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p227 : ((9794944435111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT301 (i+1))
      = (∑ i ∈ Finset.range 226, stT301 (i+1)) + stT301 227 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 226
    simpa using h
  have hprev := st301_p226
  have hstep := st301_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p228 : ((10094913183949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT301 (i+1))
      = (∑ i ∈ Finset.range 227, stT301 (i+1)) + stT301 228 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 227
    simpa using h
  have hprev := st301_p227
  have hstep := st301_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p229 : ((2061069738719/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT301 (i+1))
      = (∑ i ∈ Finset.range 228, stT301 (i+1)) + stT301 229 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 228
    simpa using h
  have hprev := st301_p228
  have hstep := st301_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p230 : ((10113497835359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT301 (i+1))
      = (∑ i ∈ Finset.range 229, stT301 (i+1)) + stT301 230 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 229
    simpa using h
  have hprev := st301_p229
  have hstep := st301_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p231 : ((9805118364767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT301 (i+1))
      = (∑ i ∈ Finset.range 230, stT301 (i+1)) + stT301 231 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 230
    simpa using h
  have hprev := st301_p230
  have hstep := st301_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p232 : ((9833091880223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT301 (i+1))
      = (∑ i ∈ Finset.range 231, stT301 (i+1)) + stT301 232 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 231
    simpa using h
  have hprev := st301_p231
  have hstep := st301_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p233 : ((20309357318769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT301 (i+1))
      = (∑ i ∈ Finset.range 232, stT301 (i+1)) + stT301 233 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 232
    simpa using h
  have hprev := st301_p232
  have hstep := st301_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p234 : ((20606778999729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT301 (i+1))
      = (∑ i ∈ Finset.range 233, stT301 (i+1)) + stT301 234 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 233
    simpa using h
  have hprev := st301_p233
  have hstep := st301_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p235 : ((20133729578799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT301 (i+1))
      = (∑ i ∈ Finset.range 234, stT301 (i+1)) + stT301 235 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 234
    simpa using h
  have hprev := st301_p234
  have hstep := st301_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p236 : ((4892067482731/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT301 (i+1))
      = (∑ i ∈ Finset.range 235, stT301 (i+1)) + stT301 236 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 235
    simpa using h
  have hprev := st301_p235
  have hstep := st301_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p237 : ((9855106224833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT301 (i+1))
      = (∑ i ∈ Finset.range 236, stT301 (i+1)) + stT301 237 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 236
    simpa using h
  have hprev := st301_p236
  have hstep := st301_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p238 : ((5089029230457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT301 (i+1))
      = (∑ i ∈ Finset.range 237, stT301 (i+1)) + stT301 238 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 237
    simpa using h
  have hprev := st301_p237
  have hstep := st301_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p239 : ((2575379357253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT301 (i+1))
      = (∑ i ∈ Finset.range 238, stT301 (i+1)) + stT301 239 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 238
    simpa using h
  have hprev := st301_p238
  have hstep := st301_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p240 : ((10055837339973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT301 (i+1))
      = (∑ i ∈ Finset.range 239, stT301 (i+1)) + stT301 240 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 239
    simpa using h
  have hprev := st301_p239
  have hstep := st301_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p241 : ((9780518196603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT301 (i+1))
      = (∑ i ∈ Finset.range 240, stT301 (i+1)) + stT301 241 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 240
    simpa using h
  have hprev := st301_p240
  have hstep := st301_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p242 : ((9851057524007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT301 (i+1))
      = (∑ i ∈ Finset.range 241, stT301 (i+1)) + stT301 242 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 241
    simpa using h
  have hprev := st301_p241
  have hstep := st301_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p243 : ((10169900023757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT301 (i+1))
      = (∑ i ∈ Finset.range 242, stT301 (i+1)) + stT301 243 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 242
    simpa using h
  have hprev := st301_p242
  have hstep := st301_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p244 : ((2061406063477/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT301 (i+1))
      = (∑ i ∈ Finset.range 243, stT301 (i+1)) + stT301 244 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 243
    simpa using h
  have hprev := st301_p243
  have hstep := st301_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p245 : ((20160963316477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT301 (i+1))
      = (∑ i ∈ Finset.range 244, stT301 (i+1)) + stT301 245 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 244
    simpa using h
  have hprev := st301_p244
  have hstep := st301_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p246 : ((612031524097/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT301 (i+1))
      = (∑ i ∈ Finset.range 245, stT301 (i+1)) + stT301 246 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 245
    simpa using h
  have hprev := st301_p245
  have hstep := st301_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p247 : ((2455568869407/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT301 (i+1))
      = (∑ i ∈ Finset.range 246, stT301 (i+1)) + stT301 247 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 246
    simpa using h
  have hprev := st301_p246
  have hstep := st301_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p248 : ((158265711877/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT301 (i+1))
      = (∑ i ∈ Finset.range 247, stT301 (i+1)) + stT301 248 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 247
    simpa using h
  have hprev := st301_p247
  have hstep := st301_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p249 : ((2578293815097/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT301 (i+1))
      = (∑ i ∈ Finset.range 248, stT301 (i+1)) + stT301 249 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 248
    simpa using h
  have hprev := st301_p248
  have hstep := st301_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p250 : ((101382391957/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT301 (i+1))
      = (∑ i ∈ Finset.range 249, stT301 (i+1)) + stT301 250 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 249
    simpa using h
  have hprev := st301_p249
  have hstep := st301_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p251 : ((983000269179/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT301 (i+1))
      = (∑ i ∈ Finset.range 250, stT301 (i+1)) + stT301 251 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 250
    simpa using h
  have hprev := st301_p250
  have hstep := st301_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p252 : ((19561373631387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT301 (i+1))
      = (∑ i ∈ Finset.range 251, stT301 (i+1)) + stT301 252 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 251
    simpa using h
  have hprev := st301_p251
  have hstep := st301_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p253 : ((20101888897029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT301 (i+1))
      = (∑ i ∈ Finset.range 252, stT301 (i+1)) + stT301 253 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 252
    simpa using h
  have hprev := st301_p252
  have hstep := st301_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p254 : ((643773245547/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT301 (i+1))
      = (∑ i ∈ Finset.range 253, stT301 (i+1)) + stT301 254 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 253
    simpa using h
  have hprev := st301_p253
  have hstep := st301_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p255 : ((20437590327129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT301 (i+1))
      = (∑ i ∈ Finset.range 254, stT301 (i+1)) + stT301 255 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 254
    simpa using h
  have hprev := st301_p254
  have hstep := st301_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p256 : ((19817739335369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT301 (i+1))
      = (∑ i ∈ Finset.range 255, stT301 (i+1)) + stT301 256 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 255
    simpa using h
  have hprev := st301_p255
  have hstep := st301_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p257 : ((19504188572589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT301 (i+1))
      = (∑ i ∈ Finset.range 256, stT301 (i+1)) + stT301 257 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 256
    simpa using h
  have hprev := st301_p256
  have hstep := st301_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p258 : ((19877109200589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT301 (i+1))
      = (∑ i ∈ Finset.range 257, stT301 (i+1)) + stT301 258 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 257
    simpa using h
  have hprev := st301_p257
  have hstep := st301_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p259 : ((10240596168189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT301 (i+1))
      = (∑ i ∈ Finset.range 258, stT301 (i+1)) + stT301 259 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 258
    simpa using h
  have hprev := st301_p258
  have hstep := st301_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p260 : ((20589024916753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT301 (i+1))
      = (∑ i ∈ Finset.range 259, stT301 (i+1)) + stT301 260 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 259
    simpa using h
  have hprev := st301_p259
  have hstep := st301_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p261 : ((10037343069919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT301 (i+1))
      = (∑ i ∈ Finset.range 260, stT301 (i+1)) + stT301 261 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 260
    simpa using h
  have hprev := st301_p260
  have hstep := st301_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p262 : ((3910294867873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT301 (i+1))
      = (∑ i ∈ Finset.range 261, stT301 (i+1)) + stT301 262 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 261
    simpa using h
  have hprev := st301_p261
  have hstep := st301_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p263 : ((785418598673/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT301 (i+1))
      = (∑ i ∈ Finset.range 262, stT301 (i+1)) + stT301 263 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 262
    simpa using h
  have hprev := st301_p262
  have hstep := st301_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p264 : ((20224854901047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT301 (i+1))
      = (∑ i ∈ Finset.range 263, stT301 (i+1)) + stT301 264 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 263
    simpa using h
  have hprev := st301_p263
  have hstep := st301_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p265 : ((20631943283187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT301 (i+1))
      = (∑ i ∈ Finset.range 264, stT301 (i+1)) + stT301 265 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 264
    simpa using h
  have hprev := st301_p264
  have hstep := st301_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p266 : ((20387942993907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT301 (i+1))
      = (∑ i ∈ Finset.range 265, stT301 (i+1)) + stT301 266 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 265
    simpa using h
  have hprev := st301_p265
  have hstep := st301_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p267 : ((3955241561229/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT301 (i+1))
      = (∑ i ∈ Finset.range 266, stT301 (i+1)) + stT301 267 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 266
    simpa using h
  have hprev := st301_p266
  have hstep := st301_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p268 : ((19495291638753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT301 (i+1))
      = (∑ i ∈ Finset.range 267, stT301 (i+1)) + stT301 268 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 267
    simpa using h
  have hprev := st301_p267
  have hstep := st301_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p269 : ((19860957285023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT301 (i+1))
      = (∑ i ∈ Finset.range 268, stT301 (i+1)) + stT301 269 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 268
    simpa using h
  have hprev := st301_p268
  have hstep := st301_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p270 : ((20458594408043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT301 (i+1))
      = (∑ i ∈ Finset.range 269, stT301 (i+1)) + stT301 270 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 269
    simpa using h
  have hprev := st301_p269
  have hstep := st301_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p271 : ((20619763419051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT301 (i+1))
      = (∑ i ∈ Finset.range 270, stT301 (i+1)) + stT301 271 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 270
    simpa using h
  have hprev := st301_p270
  have hstep := st301_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p272 : ((20168193523071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT301 (i+1))
      = (∑ i ∈ Finset.range 271, stT301 (i+1)) + stT301 272 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 271
    simpa using h
  have hprev := st301_p271
  have hstep := st301_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p273 : ((19604695388443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT301 (i+1))
      = (∑ i ∈ Finset.range 272, stT301 (i+1)) + stT301 273 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 272
    simpa using h
  have hprev := st301_p272
  have hstep := st301_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p274 : ((19546468805457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT301 (i+1))
      = (∑ i ∈ Finset.range 273, stT301 (i+1)) + stT301 274 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 273
    simpa using h
  have hprev := st301_p273
  have hstep := st301_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p275 : ((20053860561587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT301 (i+1))
      = (∑ i ∈ Finset.range 274, stT301 (i+1)) + stT301 275 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 274
    simpa using h
  have hprev := st301_p274
  have hstep := st301_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p276 : ((20575610211071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT301 (i+1))
      = (∑ i ∈ Finset.range 275, stT301 (i+1)) + stT301 276 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 275
    simpa using h
  have hprev := st301_p275
  have hstep := st301_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p277 : ((20551711720521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT301 (i+1))
      = (∑ i ∈ Finset.range 276, stT301 (i+1)) + stT301 277 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 276
    simpa using h
  have hprev := st301_p276
  have hstep := st301_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p278 : ((10005335160613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT301 (i+1))
      = (∑ i ∈ Finset.range 277, stT301 (i+1)) + stT301 278 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 277
    simpa using h
  have hprev := st301_p277
  have hstep := st301_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p279 : ((19528393033941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT301 (i+1))
      = (∑ i ∈ Finset.range 278, stT301 (i+1)) + stT301 279 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 278
    simpa using h
  have hprev := st301_p278
  have hstep := st301_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p280 : ((19612018953803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT301 (i+1))
      = (∑ i ∈ Finset.range 279, stT301 (i+1)) + stT301 280 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 279
    simpa using h
  have hprev := st301_p279
  have hstep := st301_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p281 : ((10085423185443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT301 (i+1))
      = (∑ i ∈ Finset.range 280, stT301 (i+1)) + stT301 281 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 280
    simpa using h
  have hprev := st301_p280
  have hstep := st301_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p282 : ((20621593159989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT301 (i+1))
      = (∑ i ∈ Finset.range 281, stT301 (i+1)) + stT301 282 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 281
    simpa using h
  have hprev := st301_p281
  have hstep := st301_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p283 : ((204995245169/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT301 (i+1))
      = (∑ i ∈ Finset.range 282, stT301 (i+1)) + stT301 283 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 282
    simpa using h
  have hprev := st301_p282
  have hstep := st301_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p284 : ((3986597485321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT301 (i+1))
      = (∑ i ∈ Finset.range 283, stT301 (i+1)) + stT301 284 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 283
    simpa using h
  have hprev := st301_p283
  have hstep := st301_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p285 : ((19501803557827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT301 (i+1))
      = (∑ i ∈ Finset.range 284, stT301 (i+1)) + stT301 285 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 284
    simpa using h
  have hprev := st301_p284
  have hstep := st301_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p286 : ((19641825056803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT301 (i+1))
      = (∑ i ∈ Finset.range 285, stT301 (i+1)) + stT301 286 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 285
    simpa using h
  have hprev := st301_p285
  have hstep := st301_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p287 : ((10104446628239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT301 (i+1))
      = (∑ i ∈ Finset.range 286, stT301 (i+1)) + stT301 287 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 286
    simpa using h
  have hprev := st301_p286
  have hstep := st301_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p288 : ((5158383789547/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT301 (i+1))
      = (∑ i ∈ Finset.range 287, stT301 (i+1)) + stT301 288 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 287
    simpa using h
  have hprev := st301_p287
  have hstep := st301_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p289 : ((1280908400197/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT301 (i+1))
      = (∑ i ∈ Finset.range 288, stT301 (i+1)) + stT301 289 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 288
    simpa using h
  have hprev := st301_p288
  have hstep := st301_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p290 : ((9966106373997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT301 (i+1))
      = (∑ i ∈ Finset.range 289, stT301 (i+1)) + stT301 290 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 289
    simpa using h
  have hprev := st301_p289
  have hstep := st301_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p291 : ((19500655347803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT301 (i+1))
      = (∑ i ∈ Finset.range 290, stT301 (i+1)) + stT301 291 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 290
    simpa using h
  have hprev := st301_p290
  have hstep := st301_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p292 : ((1226245337103/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT301 (i+1))
      = (∑ i ∈ Finset.range 291, stT301 (i+1)) + stT301 292 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 291
    simpa using h
  have hprev := st301_p291
  have hstep := st301_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p293 : ((10085664989683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT301 (i+1))
      = (∑ i ∈ Finset.range 292, stT301 (i+1)) + stT301 293 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 292
    simpa using h
  have hprev := st301_p292
  have hstep := st301_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p294 : ((10310693454767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT301 (i+1))
      = (∑ i ∈ Finset.range 293, stT301 (i+1)) + stT301 294 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 293
    simpa using h
  have hprev := st301_p293
  have hstep := st301_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p295 : ((641869914463/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT301 (i+1))
      = (∑ i ∈ Finset.range 294, stT301 (i+1)) + stT301 295 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 294
    simpa using h
  have hprev := st301_p294
  have hstep := st301_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p296 : ((2500890011817/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT301 (i+1))
      = (∑ i ∈ Finset.range 295, stT301 (i+1)) + stT301 296 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 295
    simpa using h
  have hprev := st301_p295
  have hstep := st301_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p297 : ((19529279709331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT301 (i+1))
      = (∑ i ∈ Finset.range 296, stT301 (i+1)) + stT301 297 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 296
    simpa using h
  have hprev := st301_p296
  have hstep := st301_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p298 : ((19554923453443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT301 (i+1))
      = (∑ i ∈ Finset.range 297, stT301 (i+1)) + stT301 298 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 297
    simpa using h
  have hprev := st301_p297
  have hstep := st301_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p299 : ((20057301933673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT301 (i+1))
      = (∑ i ∈ Finset.range 298, stT301 (i+1)) + stT301 299 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 298
    simpa using h
  have hprev := st301_p298
  have hstep := st301_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p300 : ((20567478415873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT301 (i+1))
      = (∑ i ∈ Finset.range 299, stT301 (i+1)) + stT301 300 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 299
    simpa using h
  have hprev := st301_p299
  have hstep := st301_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p301 : ((20614719916663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT301 (i+1))
      = (∑ i ∈ Finset.range 300, stT301 (i+1)) + stT301 301 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 300
    simpa using h
  have hprev := st301_p300
  have hstep := st301_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p302 : ((20158171296007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT301 (i+1))
      = (∑ i ∈ Finset.range 301, stT301 (i+1)) + stT301 302 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 301
    simpa using h
  have hprev := st301_p301
  have hstep := st301_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p303 : ((4904150640763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT301 (i+1))
      = (∑ i ∈ Finset.range 302, stT301 (i+1)) + stT301 303 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 302
    simpa using h
  have hprev := st301_p302
  have hstep := st301_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p304 : ((2435125707839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT301 (i+1))
      = (∑ i ∈ Finset.range 303, stT301 (i+1)) + stT301 304 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 303
    simpa using h
  have hprev := st301_p303
  have hstep := st301_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p305 : ((4967803505443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT301 (i+1))
      = (∑ i ∈ Finset.range 304, stT301 (i+1)) + stT301 305 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 304
    simpa using h
  have hprev := st301_p304
  have hstep := st301_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p306 : ((5108777394687/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT301 (i+1))
      = (∑ i ∈ Finset.range 305, stT301 (i+1)) + stT301 306 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 305
    simpa using h
  have hprev := st301_p305
  have hstep := st301_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p307 : ((10335019298959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT301 (i+1))
      = (∑ i ∈ Finset.range 306, stT301 (i+1)) + stT301 307 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 306
    simpa using h
  have hprev := st301_p306
  have hstep := st301_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p308 : ((20369969511861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT301 (i+1))
      = (∑ i ∈ Finset.range 307, stT301 (i+1)) + stT301 308 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 307
    simpa using h
  have hprev := st301_p307
  have hstep := st301_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p309 : ((3960300076341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT301 (i+1))
      = (∑ i ∈ Finset.range 308, stT301 (i+1)) + stT301 309 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 308
    simpa using h
  have hprev := st301_p308
  have hstep := st301_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p310 : ((19462774660449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT301 (i+1))
      = (∑ i ∈ Finset.range 309, stT301 (i+1)) + stT301 310 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 309
    simpa using h
  have hprev := st301_p309
  have hstep := st301_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p311 : ((9823383617887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT301 (i+1))
      = (∑ i ∈ Finset.range 310, stT301 (i+1)) + stT301 311 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 310
    simpa using h
  have hprev := st301_p310
  have hstep := st301_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p312 : ((10095867535701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT301 (i+1))
      = (∑ i ∈ Finset.range 311, stT301 (i+1)) + stT301 312 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 311
    simpa using h
  have hprev := st301_p311
  have hstep := st301_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p313 : ((10313943470829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT301 (i+1))
      = (∑ i ∈ Finset.range 312, stT301 (i+1)) + stT301 313 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 312
    simpa using h
  have hprev := st301_p312
  have hstep := st301_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p314 : ((10291768569927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT301 (i+1))
      = (∑ i ∈ Finset.range 313, stT301 (i+1)) + stT301 314 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 313
    simpa using h
  have hprev := st301_p313
  have hstep := st301_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p315 : ((20098812852191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT301 (i+1))
      = (∑ i ∈ Finset.range 314, stT301 (i+1)) + stT301 315 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 314
    simpa using h
  have hprev := st301_p314
  have hstep := st301_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p316 : ((19584854652383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT301 (i+1))
      = (∑ i ∈ Finset.range 315, stT301 (i+1)) + stT301 316 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 315
    simpa using h
  have hprev := st301_p315
  have hstep := st301_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p317 : ((19472732950071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT301 (i+1))
      = (∑ i ∈ Finset.range 316, stT301 (i+1)) + stT301 317 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 316
    simpa using h
  have hprev := st301_p316
  have hstep := st301_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p318 : ((19853751728559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT301 (i+1))
      = (∑ i ∈ Finset.range 317, stT301 (i+1)) + stT301 318 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 317
    simpa using h
  have hprev := st301_p317
  have hstep := st301_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p319 : ((20409464134779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT301 (i+1))
      = (∑ i ∈ Finset.range 318, stT301 (i+1)) + stT301 319 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 318
    simpa using h
  have hprev := st301_p318
  have hstep := st301_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p320 : ((20680983237123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT301 (i+1))
      = (∑ i ∈ Finset.range 319, stT301 (i+1)) + stT301 320 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 319
    simpa using h
  have hprev := st301_p319
  have hstep := st301_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p321 : ((20447293088383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT301 (i+1))
      = (∑ i ∈ Finset.range 320, stT301 (i+1)) + stT301 321 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 320
    simpa using h
  have hprev := st301_p320
  have hstep := st301_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p322 : ((3980272949411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT301 (i+1))
      = (∑ i ∈ Finset.range 321, stT301 (i+1)) + stT301 322 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 321
    simpa using h
  have hprev := st301_p321
  have hstep := st301_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p323 : ((974346535951/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT301 (i+1))
      = (∑ i ∈ Finset.range 322, stT301 (i+1)) + stT301 323 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 322
    simpa using h
  have hprev := st301_p322
  have hstep := st301_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p324 : ((3907397133793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT301 (i+1))
      = (∑ i ∈ Finset.range 323, stT301 (i+1)) + stT301 324 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 323
    simpa using h
  have hprev := st301_p323
  have hstep := st301_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p325 : ((4001795757913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT301 (i+1))
      = (∑ i ∈ Finset.range 324, stT301 (i+1)) + stT301 325 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 324
    simpa using h
  have hprev := st301_p324
  have hstep := st301_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p326 : ((20524925863229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT301 (i+1))
      = (∑ i ∈ Finset.range 325, stT301 (i+1)) + stT301 326 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 325
    simpa using h
  have hprev := st301_p325
  have hstep := st301_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p327 : ((2584517514459/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT301 (i+1))
      = (∑ i ∈ Finset.range 326, stT301 (i+1)) + stT301 327 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 326
    simpa using h
  have hprev := st301_p326
  have hstep := st301_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p328 : ((5086360135499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT301 (i+1))
      = (∑ i ∈ Finset.range 327, stT301 (i+1)) + stT301 328 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 327
    simpa using h
  have hprev := st301_p327
  have hstep := st301_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p329 : ((19794110413/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT301 (i+1))
      = (∑ i ∈ Finset.range 328, stT301 (i+1)) + stT301 329 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 328
    simpa using h
  have hprev := st301_p328
  have hstep := st301_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p330 : ((9726153390503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT301 (i+1))
      = (∑ i ∈ Finset.range 329, stT301 (i+1)) + stT301 330 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 329
    simpa using h
  have hprev := st301_p329
  have hstep := st301_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p331 : ((979170617919/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT301 (i+1))
      = (∑ i ∈ Finset.range 330, stT301 (i+1)) + stT301 331 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 330
    simpa using h
  have hprev := st301_p330
  have hstep := st301_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p332 : ((10042032767247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT301 (i+1))
      = (∑ i ∈ Finset.range 331, stT301 (i+1)) + stT301 332 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 331
    simpa using h
  have hprev := st301_p331
  have hstep := st301_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p333 : ((10284607306617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT301 (i+1))
      = (∑ i ∈ Finset.range 332, stT301 (i+1)) + stT301 333 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 332
    simpa using h
  have hprev := st301_p332
  have hstep := st301_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p334 : ((10334862047317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT301 (i+1))
      = (∑ i ∈ Finset.range 333, stT301 (i+1)) + stT301 334 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 333
    simpa using h
  have hprev := st301_p333
  have hstep := st301_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p335 : ((4062290819523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT301 (i+1))
      = (∑ i ∈ Finset.range 334, stT301 (i+1)) + stT301 335 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 334
    simpa using h
  have hprev := st301_p334
  have hstep := st301_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p336 : ((988316103759/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT301 (i+1))
      = (∑ i ∈ Finset.range 335, stT301 (i+1)) + stT301 336 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 335
    simpa using h
  have hprev := st301_p335
  have hstep := st301_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p337 : ((1944319181/1000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT301 (i+1))
      = (∑ i ∈ Finset.range 336, stT301 (i+1)) + stT301 337 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 336
    simpa using h
  have hprev := st301_p336
  have hstep := st301_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p338 : ((76489701813/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT301 (i+1))
      = (∑ i ∈ Finset.range 337, stT301 (i+1)) + stT301 338 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 337
    simpa using h
  have hprev := st301_p337
  have hstep := st301_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p339 : ((5019051212907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT301 (i+1))
      = (∑ i ∈ Finset.range 338, stT301 (i+1)) + stT301 339 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 338
    simpa using h
  have hprev := st301_p338
  have hstep := st301_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p340 : ((10280812021061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT301 (i+1))
      = (∑ i ∈ Finset.range 339, stT301 (i+1)) + stT301 340 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 339
    simpa using h
  have hprev := st301_p339
  have hstep := st301_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p341 : ((2585287526489/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT301 (i+1))
      = (∑ i ∈ Finset.range 340, stT301 (i+1)) + stT301 341 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 340
    simpa using h
  have hprev := st301_p340
  have hstep := st301_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p342 : ((5088042600147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT301 (i+1))
      = (∑ i ∈ Finset.range 341, stT301 (i+1)) + stT301 342 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 341
    simpa using h
  have hprev := st301_p341
  have hstep := st301_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p343 : ((1238281525893/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT301 (i+1))
      = (∑ i ∈ Finset.range 342, stT301 (i+1)) + stT301 343 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 342
    simpa using h
  have hprev := st301_p342
  have hstep := st301_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p344 : ((607904248209/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT301 (i+1))
      = (∑ i ∈ Finset.range 343, stT301 (i+1)) + stT301 344 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 343
    simpa using h
  have hprev := st301_p343
  have hstep := st301_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p345 : ((19530054175509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT301 (i+1))
      = (∑ i ∈ Finset.range 344, stT301 (i+1)) + stT301 345 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 344
    simpa using h
  have hprev := st301_p344
  have hstep := st301_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p346 : ((3997337972577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT301 (i+1))
      = (∑ i ∈ Finset.range 345, stT301 (i+1)) + stT301 346 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 345
    simpa using h
  have hprev := st301_p345
  have hstep := st301_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p347 : ((20497396886061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT301 (i+1))
      = (∑ i ∈ Finset.range 346, stT301 (i+1)) + stT301 347 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 346
    simpa using h
  have hprev := st301_p346
  have hstep := st301_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p348 : ((20701986946909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT301 (i+1))
      = (∑ i ∈ Finset.range 347, stT301 (i+1)) + stT301 348 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 347
    simpa using h
  have hprev := st301_p347
  have hstep := st301_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p349 : ((4091708877593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT301 (i+1))
      = (∑ i ∈ Finset.range 348, stT301 (i+1)) + stT301 349 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 348
    simpa using h
  have hprev := st301_p348
  have hstep := st301_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p350 : ((9969489472537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT301 (i+1))
      = (∑ i ∈ Finset.range 349, stT301 (i+1)) + stT301 350 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 349
    simpa using h
  have hprev := st301_p349
  have hstep := st301_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p351 : ((19504890872931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT301 (i+1))
      = (∑ i ∈ Finset.range 350, stT301 (i+1)) + stT301 351 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 350
    simpa using h
  have hprev := st301_p350
  have hstep := st301_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p352 : ((19455206025497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT301 (i+1))
      = (∑ i ∈ Finset.range 351, stT301 (i+1)) + stT301 352 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 351
    simpa using h
  have hprev := st301_p351
  have hstep := st301_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p353 : ((19822081064313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT301 (i+1))
      = (∑ i ∈ Finset.range 352, stT301 (i+1)) + stT301 353 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 352
    simpa using h
  have hprev := st301_p352
  have hstep := st301_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p354 : ((20353067487543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT301 (i+1))
      = (∑ i ∈ Finset.range 353, stT301 (i+1)) + stT301 354 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 353
    simpa using h
  have hprev := st301_p353
  have hstep := st301_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p355 : ((20686898563871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT301 (i+1))
      = (∑ i ∈ Finset.range 354, stT301 (i+1)) + stT301 355 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 354
    simpa using h
  have hprev := st301_p354
  have hstep := st301_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p356 : ((1029954707977/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT301 (i+1))
      = (∑ i ∈ Finset.range 355, stT301 (i+1)) + stT301 356 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 355
    simpa using h
  have hprev := st301_p355
  have hstep := st301_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p357 : ((5037667380659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT301 (i+1))
      = (∑ i ∈ Finset.range 356, stT301 (i+1)) + stT301 357 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 356
    simpa using h
  have hprev := st301_p356
  have hstep := st301_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p358 : ((4910736623871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT301 (i+1))
      = (∑ i ∈ Finset.range 357, stT301 (i+1)) + stT301 358 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 357
    simpa using h
  have hprev := st301_p357
  have hstep := st301_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p359 : ((2426702403043/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT301 (i+1))
      = (∑ i ∈ Finset.range 358, stT301 (i+1)) + stT301 359 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 358
    simpa using h
  have hprev := st301_p358
  have hstep := st301_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p360 : ((1961292219629/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT301 (i+1))
      = (∑ i ∈ Finset.range 359, stT301 (i+1)) + stT301 360 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 359
    simpa using h
  have hprev := st301_p359
  have hstep := st301_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p361 : ((4021529027683/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT301 (i+1))
      = (∑ i ∈ Finset.range 360, stT301 (i+1)) + stT301 361 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 360
    simpa using h
  have hprev := st301_p360
  have hstep := st301_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p362 : ((4114527619579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT301 (i+1))
      = (∑ i ∈ Finset.range 361, stT301 (i+1)) + stT301 362 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 361
    simpa using h
  have hprev := st301_p361
  have hstep := st301_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p363 : ((10352679839921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT301 (i+1))
      = (∑ i ∈ Finset.range 362, stT301 (i+1)) + stT301 363 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 362
    simpa using h
  have hprev := st301_p362
  have hstep := st301_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p364 : ((816857906607/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT301 (i+1))
      = (∑ i ∈ Finset.range 363, stT301 (i+1)) + stT301 364 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 363
    simpa using h
  have hprev := st301_p363
  have hstep := st301_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p365 : ((19905757778199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT301 (i+1))
      = (∑ i ∈ Finset.range 364, stT301 (i+1)) + stT301 365 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 364
    simpa using h
  have hprev := st301_p364
  have hstep := st301_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p366 : ((9744925124603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT301 (i+1))
      = (∑ i ∈ Finset.range 365, stT301 (i+1)) + stT301 366 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 365
    simpa using h
  have hprev := st301_p365
  have hstep := st301_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p367 : ((9719184979847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT301 (i+1))
      = (∑ i ∈ Finset.range 366, stT301 (i+1)) + stT301 367 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 366
    simpa using h
  have hprev := st301_p366
  have hstep := st301_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p368 : ((9891095198213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT301 (i+1))
      = (∑ i ∈ Finset.range 367, stT301 (i+1)) + stT301 368 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 367
    simpa using h
  have hprev := st301_p367
  have hstep := st301_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p369 : ((20302423211391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT301 (i+1))
      = (∑ i ∈ Finset.range 368, stT301 (i+1)) + stT301 369 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 368
    simpa using h
  have hprev := st301_p368
  have hstep := st301_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p370 : ((20671583329641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT301 (i+1))
      = (∑ i ∈ Finset.range 369, stT301 (i+1)) + stT301 370 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 369
    simpa using h
  have hprev := st301_p369
  have hstep := st301_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p371 : ((20659785596941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT301 (i+1))
      = (∑ i ∈ Finset.range 370, stT301 (i+1)) + stT301 371 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 370
    simpa using h
  have hprev := st301_p370
  have hstep := st301_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p372 : ((20276135651409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT301 (i+1))
      = (∑ i ∈ Finset.range 371, stT301 (i+1)) + stT301 372 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 371
    simpa using h
  have hprev := st301_p371
  have hstep := st301_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p373 : ((19759575579007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT301 (i+1))
      = (∑ i ∈ Finset.range 372, stT301 (i+1)) + stT301 373 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 372
    simpa using h
  have hprev := st301_p372
  have hstep := st301_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p374 : ((3885693310323/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT301 (i+1))
      = (∑ i ∈ Finset.range 373, stT301 (i+1)) + stT301 374 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 373
    simpa using h
  have hprev := st301_p373
  have hstep := st301_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p375 : ((19484568954489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT301 (i+1))
      = (∑ i ∈ Finset.range 374, stT301 (i+1)) + stT301 375 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 374
    simpa using h
  have hprev := st301_p374
  have hstep := st301_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p376 : ((19891846285599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT301 (i+1))
      = (∑ i ∈ Finset.range 375, stT301 (i+1)) + stT301 376 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 375
    simpa using h
  have hprev := st301_p375
  have hstep := st301_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p377 : ((816073536859/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT301 (i+1))
      = (∑ i ∈ Finset.range 376, stT301 (i+1)) + stT301 377 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 376
    simpa using h
  have hprev := st301_p376
  have hstep := st301_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p378 : ((20706568210747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT301 (i+1))
      = (∑ i ∈ Finset.range 377, stT301 (i+1)) + stT301 378 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 377
    simpa using h
  have hprev := st301_p377
  have hstep := st301_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p379 : ((20624155637707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT301 (i+1))
      = (∑ i ∈ Finset.range 378, stT301 (i+1)) + stT301 379 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 378
    simpa using h
  have hprev := st301_p378
  have hstep := st301_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p380 : ((20205589655047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT301 (i+1))
      = (∑ i ∈ Finset.range 379, stT301 (i+1)) + stT301 380 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 379
    simpa using h
  have hprev := st301_p379
  have hstep := st301_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p381 : ((19700996818747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT301 (i+1))
      = (∑ i ∈ Finset.range 380, stT301 (i+1)) + stT301 381 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 380
    simpa using h
  have hprev := st301_p380
  have hstep := st301_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p382 : ((19408951899327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT301 (i+1))
      = (∑ i ∈ Finset.range 381, stT301 (i+1)) + stT301 382 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 381
    simpa using h
  have hprev := st301_p381
  have hstep := st301_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p383 : ((3900030996723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT301 (i+1))
      = (∑ i ∈ Finset.range 382, stT301 (i+1)) + stT301 383 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 382
    simpa using h
  have hprev := st301_p382
  have hstep := st301_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p384 : ((3983888095721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT301 (i+1))
      = (∑ i ∈ Finset.range 383, stT301 (i+1)) + stT301 384 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 383
    simpa using h
  have hprev := st301_p383
  have hstep := st301_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p385 : ((10210560083527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT301 (i+1))
      = (∑ i ∈ Finset.range 384, stT301 (i+1)) + stT301 385 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 384
    simpa using h
  have hprev := st301_p384
  have hstep := st301_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p386 : ((2589264681121/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT301 (i+1))
      = (∑ i ∈ Finset.range 385, stT301 (i+1)) + stT301 386 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 385
    simpa using h
  have hprev := st301_p385
  have hstep := st301_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p387 : ((10315221722797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT301 (i+1))
      = (∑ i ∈ Finset.range 386, stT301 (i+1)) + stT301 387 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 386
    simpa using h
  have hprev := st301_p386
  have hstep := st301_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p388 : ((9872951033/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT301 (i+1))
      = (∑ i ∈ Finset.range 387, stT301 (i+1)) + stT301 388 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 387
    simpa using h
  have hprev := st301_p387
  have hstep := st301_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p389 : ((19718128237987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT301 (i+1))
      = (∑ i ∈ Finset.range 388, stT301 (i+1)) + stT301 389 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 388
    simpa using h
  have hprev := st301_p388
  have hstep := st301_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p390 : ((19410830514307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT301 (i+1))
      = (∑ i ∈ Finset.range 389, stT301 (i+1)) + stT301 390 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 389
    simpa using h
  have hprev := st301_p389
  have hstep := st301_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p391 : ((9735363801913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT301 (i+1))
      = (∑ i ∈ Finset.range 390, stT301 (i+1)) + stT301 391 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 390
    simpa using h
  have hprev := st301_p390
  have hstep := st301_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p392 : ((9931206515837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT301 (i+1))
      = (∑ i ∈ Finset.range 391, stT301 (i+1)) + stT301 392 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 391
    simpa using h
  have hprev := st301_p391
  have hstep := st301_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p393 : ((20365027550709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT301 (i+1))
      = (∑ i ∈ Finset.range 392, stT301 (i+1)) + stT301 393 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 392
    simpa using h
  have hprev := st301_p392
  have hstep := st301_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p394 : ((20697968569749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT301 (i+1))
      = (∑ i ∈ Finset.range 393, stT301 (i+1)) + stT301 394 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 393
    simpa using h
  have hprev := st301_p393
  have hstep := st301_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p395 : ((20677363366189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT301 (i+1))
      = (∑ i ∈ Finset.range 394, stT301 (i+1)) + stT301 395 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 394
    simpa using h
  have hprev := st301_p394
  have hstep := st301_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p396 : ((20316148688837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT301 (i+1))
      = (∑ i ∈ Finset.range 395, stT301 (i+1)) + stT301 396 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 395
    simpa using h
  have hprev := st301_p395
  have hstep := st301_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p397 : ((19814236088879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT301 (i+1))
      = (∑ i ∈ Finset.range 396, stT301 (i+1)) + stT301 397 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 396
    simpa using h
  have hprev := st301_p396
  have hstep := st301_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p398 : ((9723289038877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT301 (i+1))
      = (∑ i ∈ Finset.range 397, stT301 (i+1)) + stT301 398 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 397
    simpa using h
  have hprev := st301_p397
  have hstep := st301_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p399 : ((19412539947397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT301 (i+1))
      = (∑ i ∈ Finset.range 398, stT301 (i+1)) + stT301 399 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 398
    simpa using h
  have hprev := st301_p398
  have hstep := st301_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p400 : ((19729015947397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT301 (i+1))
      = (∑ i ∈ Finset.range 399, stT301 (i+1)) + stT301 400 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 399
    simpa using h
  have hprev := st301_p399
  have hstep := st301_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p401 : ((20223882582117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT301 (i+1))
      = (∑ i ∈ Finset.range 400, stT301 (i+1)) + stT301 401 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 400
    simpa using h
  have hprev := st301_p400
  have hstep := st301_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p402 : ((20630933676661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT301 (i+1))
      = (∑ i ∈ Finset.range 401, stT301 (i+1)) + stT301 402 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 401
    simpa using h
  have hprev := st301_p401
  have hstep := st301_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p403 : ((10366639001543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT301 (i+1))
      = (∑ i ∈ Finset.range 402, stT301 (i+1)) + stT301 403 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 402
    simpa using h
  have hprev := st301_p402
  have hstep := st301_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p404 : ((2047788955993/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT301 (i+1))
      = (∑ i ∈ Finset.range 403, stT301 (i+1)) + stT301 404 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 403
    simpa using h
  have hprev := st301_p403
  have hstep := st301_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p405 : ((10000681548033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT301 (i+1))
      = (∑ i ∈ Finset.range 404, stT301 (i+1)) + stT301 405 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 404
    simpa using h
  have hprev := st301_p404
  have hstep := st301_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p406 : ((9777709959733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT301 (i+1))
      = (∑ i ∈ Finset.range 405, stT301 (i+1)) + stT301 406 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 405
    simpa using h
  have hprev := st301_p405
  have hstep := st301_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p407 : ((9686730998407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT301 (i+1))
      = (∑ i ∈ Finset.range 406, stT301 (i+1)) + stT301 407 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 406
    simpa using h
  have hprev := st301_p406
  have hstep := st301_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p408 : ((19549151027689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT301 (i+1))
      = (∑ i ∈ Finset.range 407, stT301 (i+1)) + stT301 408 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 407
    simpa using h
  have hprev := st301_p407
  have hstep := st301_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p409 : ((3997943117521/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT301 (i+1))
      = (∑ i ∈ Finset.range 408, stT301 (i+1)) + stT301 409 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 408
    simpa using h
  have hprev := st301_p408
  have hstep := st301_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p410 : ((20466422258381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT301 (i+1))
      = (∑ i ∈ Finset.range 409, stT301 (i+1)) + stT301 410 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 409
    simpa using h
  have hprev := st301_p409
  have hstep := st301_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p411 : ((2591753227669/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT301 (i+1))
      = (∑ i ∈ Finset.range 410, stT301 (i+1)) + stT301 411 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 410
    simpa using h
  have hprev := st301_p410
  have hstep := st301_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p412 : ((20656502520277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT301 (i+1))
      = (∑ i ∈ Finset.range 411, stT301 (i+1)) + stT301 412 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 411
    simpa using h
  have hprev := st301_p411
  have hstep := st301_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p413 : ((20274827023669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT301 (i+1))
      = (∑ i ∈ Finset.range 412, stT301 (i+1)) + stT301 413 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 412
    simpa using h
  have hprev := st301_p412
  have hstep := st301_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p414 : ((19783795841743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT301 (i+1))
      = (∑ i ∈ Finset.range 413, stT301 (i+1)) + stT301 414 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 413
    simpa using h
  have hprev := st301_p413
  have hstep := st301_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p415 : ((971582798747/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT301 (i+1))
      = (∑ i ∈ Finset.range 414, stT301 (i+1)) + stT301 415 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 414
    simpa using h
  have hprev := st301_p414
  have hstep := st301_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p416 : ((19394649300551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT301 (i+1))
      = (∑ i ∈ Finset.range 415, stT301 (i+1)) + stT301 416 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 415
    simpa using h
  have hprev := st301_p415
  have hstep := st301_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p417 : ((19689888187841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT301 (i+1))
      = (∑ i ∈ Finset.range 416, stT301 (i+1)) + stT301 417 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 416
    simpa using h
  have hprev := st301_p416
  have hstep := st301_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p418 : ((5042237846369/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT301 (i+1))
      = (∑ i ∈ Finset.range 417, stT301 (i+1)) + stT301 418 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 417
    simpa using h
  have hprev := st301_p417
  have hstep := st301_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p419 : ((823746799109/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT301 (i+1))
      = (∑ i ∈ Finset.range 418, stT301 (i+1)) + stT301 419 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 418
    simpa using h
  have hprev := st301_p418
  have hstep := st301_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p420 : ((166038336349/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT301 (i+1))
      = (∑ i ∈ Finset.range 419, stT301 (i+1)) + stT301 420 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 419
    simpa using h
  have hprev := st301_p419
  have hstep := st301_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p421 : ((5143584148763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT301 (i+1))
      = (∑ i ∈ Finset.range 420, stT301 (i+1)) + stT301 421 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 420
    simpa using h
  have hprev := st301_p420
  have hstep := st301_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p422 : ((1258871358701/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT301 (i+1))
      = (∑ i ∈ Finset.range 421, stT301 (i+1)) + stT301 422 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 421
    simpa using h
  have hprev := st301_p421
  have hstep := st301_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p423 : ((3933806207971/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT301 (i+1))
      = (∑ i ∈ Finset.range 422, stT301 (i+1)) + stT301 423 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 422
    simpa using h
  have hprev := st301_p422
  have hstep := st301_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p424 : ((3876956838391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT301 (i+1))
      = (∑ i ∈ Finset.range 423, stT301 (i+1)) + stT301 424 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 423
    simpa using h
  have hprev := st301_p423
  have hstep := st301_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p425 : ((3885080807499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT301 (i+1))
      = (∑ i ∈ Finset.range 424, stT301 (i+1)) + stT301 425 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 424
    simpa using h
  have hprev := st301_p424
  have hstep := st301_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p426 : ((19769982117697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT301 (i+1))
      = (∑ i ∈ Finset.range 425, stT301 (i+1)) + stT301 426 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 425
    simpa using h
  have hprev := st301_p425
  have hstep := st301_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p427 : ((4050510666047/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT301 (i+1))
      = (∑ i ∈ Finset.range 426, stT301 (i+1)) + stT301 427 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 426
    simpa using h
  have hprev := st301_p426
  have hstep := st301_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p428 : ((20642972564043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT301 (i+1))
      = (∑ i ∈ Finset.range 427, stT301 (i+1)) + stT301 428 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 427
    simpa using h
  have hprev := st301_p427
  have hstep := st301_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p429 : ((20756724566071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT301 (i+1))
      = (∑ i ∈ Finset.range 428, stT301 (i+1)) + stT301 429 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 428
    simpa using h
  have hprev := st301_p428
  have hstep := st301_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p430 : ((10270672839827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT301 (i+1))
      = (∑ i ∈ Finset.range 429, stT301 (i+1)) + stT301 430 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 429
    simpa using h
  have hprev := st301_p429
  have hstep := st301_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p431 : ((10049648764639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT301 (i+1))
      = (∑ i ∈ Finset.range 430, stT301 (i+1)) + stT301 431 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 430
    simpa using h
  have hprev := st301_p430
  have hstep := st301_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p432 : ((1227378078123/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT301 (i+1))
      = (∑ i ∈ Finset.range 431, stT301 (i+1)) + stT301 432 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 431
    simpa using h
  have hprev := st301_p431
  have hstep := st301_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p433 : ((2421527864451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT301 (i+1))
      = (∑ i ∈ Finset.range 432, stT301 (i+1)) + stT301 433 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 432
    simpa using h
  have hprev := st301_p432
  have hstep := st301_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p434 : ((19424072695863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT301 (i+1))
      = (∑ i ∈ Finset.range 433, stT301 (i+1)) + stT301 434 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 433
    simpa using h
  have hprev := st301_p433
  have hstep := st301_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p435 : ((19768330965567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT301 (i+1))
      = (∑ i ∈ Finset.range 434, stT301 (i+1)) + stT301 435 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 434
    simpa using h
  have hprev := st301_p434
  have hstep := st301_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p436 : ((809828764263/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT301 (i+1))
      = (∑ i ∈ Finset.range 435, stT301 (i+1)) + stT301 436 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 435
    simpa using h
  have hprev := st301_p435
  have hstep := st301_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p437 : ((20637486785111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT301 (i+1))
      = (∑ i ∈ Finset.range 436, stT301 (i+1)) + stT301 437 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 436
    simpa using h
  have hprev := st301_p436
  have hstep := st301_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p438 : ((20765703033777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT301 (i+1))
      = (∑ i ∈ Finset.range 437, stT301 (i+1)) + stT301 438 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 437
    simpa using h
  have hprev := st301_p437
  have hstep := st301_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p439 : ((20573371157257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT301 (i+1))
      = (∑ i ∈ Finset.range 438, stT301 (i+1)) + stT301 439 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 438
    simpa using h
  have hprev := st301_p438
  have hstep := st301_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p440 : ((20148559085913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT301 (i+1))
      = (∑ i ∈ Finset.range 439, stT301 (i+1)) + stT301 440 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 439
    simpa using h
  have hprev := st301_p439
  have hstep := st301_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p441 : ((19682984288067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT301 (i+1))
      = (∑ i ∈ Finset.range 440, stT301 (i+1)) + stT301 441 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 440
    simpa using h
  have hprev := st301_p440
  have hstep := st301_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p442 : ((19384960246599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT301 (i+1))
      = (∑ i ∈ Finset.range 441, stT301 (i+1)) + stT301 442 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 441
    simpa using h
  have hprev := st301_p441
  have hstep := st301_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p443 : ((19386446403191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT301 (i+1))
      = (∑ i ∈ Finset.range 442, stT301 (i+1)) + stT301 443 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 442
    simpa using h
  have hprev := st301_p442
  have hstep := st301_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p444 : ((19685519289277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT301 (i+1))
      = (∑ i ∈ Finset.range 443, stT301 (i+1)) + stT301 444 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 443
    simpa using h
  have hprev := st301_p443
  have hstep := st301_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p445 : ((20148932408017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT301 (i+1))
      = (∑ i ∈ Finset.range 444, stT301 (i+1)) + stT301 445 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 444
    simpa using h
  have hprev := st301_p444
  have hstep := st301_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p446 : ((4114469167713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT301 (i+1))
      = (∑ i ∈ Finset.range 445, stT301 (i+1)) + stT301 446 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 445
    simpa using h
  have hprev := st301_p445
  have hstep := st301_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p447 : ((20770646799213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT301 (i+1))
      = (∑ i ∈ Finset.range 446, stT301 (i+1)) + stT301 447 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 446
    simpa using h
  have hprev := st301_p446
  have hstep := st301_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p448 : ((20658337393629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT301 (i+1))
      = (∑ i ∈ Finset.range 447, stT301 (i+1)) + stT301 448 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 447
    simpa using h
  have hprev := st301_p447
  have hstep := st301_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p449 : ((20285404621659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT301 (i+1))
      = (∑ i ∈ Finset.range 448, stT301 (i+1)) + stT301 449 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 448
    simpa using h
  have hprev := st301_p448
  have hstep := st301_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p450 : ((4953493895001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT301 (i+1))
      = (∑ i ∈ Finset.range 449, stT301 (i+1)) + stT301 450 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 449
    simpa using h
  have hprev := st301_p449
  have hstep := st301_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p451 : ((2430899639291/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT301 (i+1))
      = (∑ i ∈ Finset.range 450, stT301 (i+1)) + stT301 451 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 450
    simpa using h
  have hprev := st301_p450
  have hstep := st301_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p452 : ((9670847100653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT301 (i+1))
      = (∑ i ∈ Finset.range 451, stT301 (i+1)) + stT301 452 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 451
    simpa using h
  have hprev := st301_p451
  have hstep := st301_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p453 : ((9770690919693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT301 (i+1))
      = (∑ i ∈ Finset.range 452, stT301 (i+1)) + stT301 453 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 452
    simpa using h
  have hprev := st301_p452
  have hstep := st301_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p454 : ((623755987653/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT301 (i+1))
      = (∑ i ∈ Finset.range 453, stT301 (i+1)) + stT301 454 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 453
    simpa using h
  have hprev := st301_p453
  have hstep := st301_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p455 : ((10210065794649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT301 (i+1))
      = (∑ i ∈ Finset.range 454, stT301 (i+1)) + stT301 455 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 454
    simpa using h
  have hprev := st301_p454
  have hstep := st301_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p456 : ((10363675638927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT301 (i+1))
      = (∑ i ∈ Finset.range 455, stT301 (i+1)) + stT301 456 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 455
    simpa using h
  have hprev := st301_p455
  have hstep := st301_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p457 : ((10376826338067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT301 (i+1))
      = (∑ i ∈ Finset.range 456, stT301 (i+1)) + stT301 457 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 456
    simpa using h
  have hprev := st301_p456
  have hstep := st301_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p458 : ((2561145070893/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT301 (i+1))
      = (∑ i ∈ Finset.range 457, stT301 (i+1)) + stT301 458 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 457
    simpa using h
  have hprev := st301_p457
  have hstep := st301_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p459 : ((10022494933011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT301 (i+1))
      = (∑ i ∈ Finset.range 458, stT301 (i+1)) + stT301 459 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 458
    simpa using h
  have hprev := st301_p458
  have hstep := st301_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p460 : ((306339737067/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT301 (i+1))
      = (∑ i ∈ Finset.range 459, stT301 (i+1)) + stT301 460 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 459
    simpa using h
  have hprev := st301_p459
  have hstep := st301_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p461 : ((19352476008399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT301 (i+1))
      = (∑ i ∈ Finset.range 460, stT301 (i+1)) + stT301 461 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 460
    simpa using h
  have hprev := st301_p460
  have hstep := st301_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p462 : ((19388395482251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT301 (i+1))
      = (∑ i ∈ Finset.range 461, stT301 (i+1)) + stT301 462 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 461
    simpa using h
  have hprev := st301_p461
  have hstep := st301_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p463 : ((246220590247/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT301 (i+1))
      = (∑ i ∈ Finset.range 462, stT301 (i+1)) + stT301 463 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 462
    simpa using h
  have hprev := st301_p462
  have hstep := st301_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p464 : ((5038300760171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT301 (i+1))
      = (∑ i ∈ Finset.range 463, stT301 (i+1)) + stT301 464 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 463
    simpa using h
  have hprev := st301_p463
  have hstep := st301_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p465 : ((205697473519/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT301 (i+1))
      = (∑ i ∈ Finset.range 464, stT301 (i+1)) + stT301 465 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 464
    simpa using h
  have hprev := st301_p464
  have hstep := st301_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p466 : ((10389613855773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT301 (i+1))
      = (∑ i ∈ Finset.range 465, stT301 (i+1)) + stT301 466 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 465
    simpa using h
  have hprev := st301_p465
  have hstep := st301_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p467 : ((20698215407141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT301 (i+1))
      = (∑ i ∈ Finset.range 466, stT301 (i+1)) + stT301 467 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 466
    simpa using h
  have hprev := st301_p466
  have hstep := st301_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p468 : ((20360286813591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT301 (i+1))
      = (∑ i ∈ Finset.range 467, stT301 (i+1)) + stT301 468 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 467
    simpa using h
  have hprev := st301_p467
  have hstep := st301_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p469 : ((19901202854169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT301 (i+1))
      = (∑ i ∈ Finset.range 468, stT301 (i+1)) + stT301 469 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 468
    simpa using h
  have hprev := st301_p468
  have hstep := st301_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p470 : ((19503757617929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT301 (i+1))
      = (∑ i ∈ Finset.range 469, stT301 (i+1)) + stT301 470 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 469
    simpa using h
  have hprev := st301_p469
  have hstep := st301_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p471 : ((19324892668697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT301 (i+1))
      = (∑ i ∈ Finset.range 470, stT301 (i+1)) + stT301 471 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 470
    simpa using h
  have hprev := st301_p470
  have hstep := st301_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p472 : ((242927341957/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT301 (i+1))
      = (∑ i ∈ Finset.range 471, stT301 (i+1)) + stT301 472 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 471
    simpa using h
  have hprev := st301_p471
  have hstep := st301_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p473 : ((123672567421/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT301 (i+1))
      = (∑ i ∈ Finset.range 472, stT301 (i+1)) + stT301 473 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 472
    simpa using h
  have hprev := st301_p472
  have hstep := st301_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p474 : ((16196881421/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT301 (i+1))
      = (∑ i ∈ Finset.range 473, stT301 (i+1)) + stT301 474 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 473
    simpa using h
  have hprev := st301_p473
  have hstep := st301_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p475 : ((2578851996187/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT301 (i+1))
      = (∑ i ∈ Finset.range 474, stT301 (i+1)) + stT301 475 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 474
    simpa using h
  have hprev := st301_p474
  have hstep := st301_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p476 : ((10396469297143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT301 (i+1))
      = (∑ i ∈ Finset.range 475, stT301 (i+1)) + stT301 476 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 475
    simpa using h
  have hprev := st301_p475
  have hstep := st301_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p477 : ((20670748467863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT301 (i+1))
      = (∑ i ∈ Finset.range 476, stT301 (i+1)) + stT301 477 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 476
    simpa using h
  have hprev := st301_p476
  have hstep := st301_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p478 : ((20312297413543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT301 (i+1))
      = (∑ i ∈ Finset.range 477, stT301 (i+1)) + stT301 478 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 477
    simpa using h
  have hprev := st301_p477
  have hstep := st301_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p479 : ((19855730382103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT301 (i+1))
      = (∑ i ∈ Finset.range 478, stT301 (i+1)) + stT301 479 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 478
    simpa using h
  have hprev := st301_p478
  have hstep := st301_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p480 : ((19475506870331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT301 (i+1))
      = (∑ i ∈ Finset.range 479, stT301 (i+1)) + stT301 480 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 479
    simpa using h
  have hprev := st301_p479
  have hstep := st301_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p481 : ((9657853337311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT301 (i+1))
      = (∑ i ∈ Finset.range 480, stT301 (i+1)) + stT301 481 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 480
    simpa using h
  have hprev := st301_p480
  have hstep := st301_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p482 : ((971795803537/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT301 (i+1))
      = (∑ i ∈ Finset.range 481, stT301 (i+1)) + stT301 482 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 481
    simpa using h
  have hprev := st301_p481
  have hstep := st301_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p483 : ((3957947419957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT301 (i+1))
      = (∑ i ∈ Finset.range 482, stT301 (i+1)) + stT301 483 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 482
    simpa using h
  have hprev := st301_p482
  have hstep := st301_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p484 : ((253043656939/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT301 (i+1))
      = (∑ i ∈ Finset.range 483, stT301 (i+1)) + stT301 484 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 483
    simpa using h
  have hprev := st301_p483
  have hstep := st301_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p485 : ((1289199854559/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT301 (i+1))
      = (∑ i ∈ Finset.range 484, stT301 (i+1)) + stT301 485 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 484
    simpa using h
  have hprev := st301_p484
  have hstep := st301_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p486 : ((1039913225673/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT301 (i+1))
      = (∑ i ∈ Finset.range 485, stT301 (i+1)) + stT301 486 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 485
    simpa using h
  have hprev := st301_p485
  have hstep := st301_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p487 : ((5173517598669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT301 (i+1))
      = (∑ i ∈ Finset.range 486, stT301 (i+1)) + stT301 487 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 486
    simpa using h
  have hprev := st301_p486
  have hstep := st301_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p488 : ((20354130646947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT301 (i+1))
      = (∑ i ∈ Finset.range 487, stT301 (i+1)) + stT301 488 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 487
    simpa using h
  have hprev := st301_p487
  have hstep := st301_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p489 : ((19904374249771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT301 (i+1))
      = (∑ i ∈ Finset.range 488, stT301 (i+1)) + stT301 489 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 488
    simpa using h
  have hprev := st301_p488
  have hstep := st301_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p490 : ((19509978099889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT301 (i+1))
      = (∑ i ∈ Finset.range 489, stT301 (i+1)) + stT301 490 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 489
    simpa using h
  have hprev := st301_p489
  have hstep := st301_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p491 : ((3862930167197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT301 (i+1))
      = (∑ i ∈ Finset.range 490, stT301 (i+1)) + stT301 491 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 490
    simpa using h
  have hprev := st301_p490
  have hstep := st301_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p492 : ((19388616465361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT301 (i+1))
      = (∑ i ∈ Finset.range 491, stT301 (i+1)) + stT301 492 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 491
    simpa using h
  have hprev := st301_p491
  have hstep := st301_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p493 : ((19704048806359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT301 (i+1))
      = (∑ i ∈ Finset.range 492, stT301 (i+1)) + stT301 493 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 492
    simpa using h
  have hprev := st301_p492
  have hstep := st301_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p494 : ((10073132454617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT301 (i+1))
      = (∑ i ∈ Finset.range 493, stT301 (i+1)) + stT301 494 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 493
    simpa using h
  have hprev := st301_p493
  have hstep := st301_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p495 : ((10277952762419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT301 (i+1))
      = (∑ i ∈ Finset.range 494, stT301 (i+1)) + stT301 495 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 494
    simpa using h
  have hprev := st301_p494
  have hstep := st301_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p496 : ((5196623139721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT301 (i+1))
      = (∑ i ∈ Finset.range 495, stT301 (i+1)) + stT301 496 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 495
    simpa using h
  have hprev := st301_p495
  have hstep := st301_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p497 : ((2594562152243/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT301 (i+1))
      = (∑ i ∈ Finset.range 496, stT301 (i+1)) + stT301 497 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 496
    simpa using h
  have hprev := st301_p496
  have hstep := st301_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p498 : ((4095507921267/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT301 (i+1))
      = (∑ i ∈ Finset.range 497, stT301 (i+1)) + stT301 498 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 497
    simpa using h
  have hprev := st301_p497
  have hstep := st301_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p499 : ((801967679333/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT301 (i+1))
      = (∑ i ∈ Finset.range 498, stT301 (i+1)) + stT301 499 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 498
    simpa using h
  have hprev := st301_p498
  have hstep := st301_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_p500 : ((19622902679171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT301 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT301 (i+1))
      = (∑ i ∈ Finset.range 499, stT301 (i+1)) + stT301 500 := by
    have h := Finset.sum_range_succ (fun i => stT301 (i+1)) 499
    simpa using h
  have hprev := st301_p499
  have hstep := st301_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st301_s500 :
    |Real.sin (((301 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))
      - ((-302621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -7085379/10000000) (δ := 7581/500000000) (ψ := 1041953/1000000) 301 298
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 301`** (evaluated boundary). -/
theorem station_301_sign : hardyG ((((301:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 301 500 (by norm_num) (by norm_num)
    ((1041953/1000000 : ℚ) : ℝ)
  have hchain := st301_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT301 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((301 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((1041953/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st301_c500
  have hsinb := abs_le.mp st301_s500
  have hbdy_lo : ((81871575940089/3624050000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((301 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ))) / 2
          - ((((301:ℕ)):ℝ))
            * Real.sin (((301 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1041953/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((301:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((301:ℝ) * Real.log (500:ℝ) - ((1041953/1000000 : ℚ) : ℝ))) / 2
        - ((301:ℝ)) * Real.sin ((301:ℝ) * Real.log (500:ℝ) - ((1041953/1000000 : ℚ) : ℝ))
        ≥ ((183070653/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((301:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((183070653/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((183070653/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((183070653/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((301:ℕ)):ℝ))+1) * (((((301:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((3532264548071/5000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((19622902679171/10000000000000 : ℚ) : ℝ) + ((81871575940089/3624050000000000 : ℚ) : ℝ)
      - ((3532264548071/5000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((1041953/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((301:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((1041953/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((301:ℕ)):ℝ)))).re
      - Real.sin ((1041953/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((301:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((301:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((301:ℕ)):ℝ))
      = (((((301:ℕ)):ℝ)) * (Real.log ((((301:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((301:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_301
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
  have hθwin : |(((1041953/1000000 : ℚ) : ℝ) + ((69:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((301:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((301:ℕ)):ℝ)))
    (φ := ((1041953/1000000 : ℚ) : ℝ) + ((69:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((1041953/1000000 : ℚ) : ℝ) + ((69:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((1041953/1000000 : ℚ)) : ℝ) - Real.pi) + ((69:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((1041953/1000000 : ℚ)) : ℝ) - Real.pi) 69).1,
    (cos_sin_shift ((((1041953/1000000 : ℚ)) : ℝ) - Real.pi) 69).2]
  exact cos_sin_flip ((1041953/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_301_sign
end AxiomAudit
