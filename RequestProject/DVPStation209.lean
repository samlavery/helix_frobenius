import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 209` (rung-217.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT209 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((209 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((73017/125000 : ℚ) : ℝ))

theorem st209_c1 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((834189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73017/500000) (δ := 1/1000000000) (ψ := 73017/125000) 209 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t1 : ((834139/1000000 : ℚ) : ℝ) ≤ stT209 1 := by
  have hc : ((834139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((834139/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((834139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c2 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((243437/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -574109/10000000) (δ := 10567/1000000000) (ψ := 73017/125000) 209 23
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t2 : ((3442541897883/5000000000000 : ℚ) : ℝ) ≤ stT209 2 := by
  have hc : ((486849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3442541897883/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((486849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c3 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-952199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7077883/10000000) (δ := 523/50000000) (ψ := 73017/125000) 209 36
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t3 : ((-5497812458247/10000000000000 : ℚ) : ℝ) ≤ stT209 3 := by
  have hc : ((-952249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5497812458247/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-952249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c4 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((198443/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78037/2500000) (δ := 1329/125000000) (ψ := 73017/125000) 209 46
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t4 : ((198433/400000 : ℚ) : ℝ) ≤ stT209 4 := by
  have hc : ((198433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198433/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((198433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c5 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-58449/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 868617/1250000) (δ := 5291/500000000) (ψ := 73017/125000) 209 53
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t5 : ((-261405852489/625000000000 : ℚ) : ℝ) ≤ stT209 5 := by
  have hc : ((-467617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261405852489/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-467617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c6 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-999029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7743823/10000000) (δ := 1329/125000000) (ψ := 73017/125000) 209 60
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t6 : ((-4078723033157/10000000000000 : ℚ) : ℝ) ≤ stT209 6 := by
  have hc : ((-999079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4078723033157/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-999079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c7 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-331629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5739899/10000000) (δ := 2617/250000000) (ψ := 73017/125000) 209 65
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t7 : ((-125353438283/500000000000 : ℚ) : ℝ) ≤ stT209 7 := by
  have hc : ((-165827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125353438283/500000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-165827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c8 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((88729/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 299601/2500000) (δ := 5303/500000000) (ψ := 73017/125000) 209 69
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t8 : ((78421657473/250000000000 : ℚ) : ℝ) ≤ stT209 8 := by
  have hc : ((22181/25000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78421657473/250000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((22181/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c9 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((39973/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91831/10000000) (δ := 5263/500000000) (ψ := 73017/125000) 209 73
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t9 : ((133236653343/400000000000 : ℚ) : ℝ) ≤ stT209 9 := by
  have hc : ((39971/40000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133236653343/400000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((39971/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c10 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-249993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391757/500000) (δ := 2639/250000000) (ψ := 73017/125000) 209 76
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t10 : ((-790586892529/2500000000000 : ℚ) : ℝ) ≤ stT209 10 := by
  have hc : ((-500011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-790586892529/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-500011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c11 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-6081/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5197133/10000000) (δ := 661/62500000) (ψ := 73017/125000) 209 80
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t11 : ((-73347170721/500000000000 : ℚ) : ℝ) ≤ stT209 11 := by
  have hc : ((-48653/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73347170721/500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-48653/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c12 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-921619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6857567/10000000) (δ := 5303/500000000) (ψ := 73017/125000) 209 83
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t12 : ((-83144682159/312500000000 : ℚ) : ℝ) ≤ stT209 12 := by
  have hc : ((-921669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83144682159/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-921669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c13 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((150693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1774409/5000000) (δ := 2653/250000000) (ψ := 73017/125000) 209 85
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t13 : ((835616721/20000000000 : ℚ) : ℝ) ≤ stT209 13 := by
  have hc : ((150643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((835616721/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((150643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c14 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-362231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2426821/5000000) (δ := 10533/1000000000) (ψ := 73017/125000) 209 88
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t14 : ((-968236910253/10000000000000 : ℚ) : ℝ) ≤ stT209 14 := by
  have hc : ((-362281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-968236910253/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-362281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c15 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((996103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110389/5000000) (δ := 1331/125000000) (ψ := 73017/125000) 209 90
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t15 : ((642949223341/2500000000000 : ℚ) : ℝ) ≤ stT209 15 := by
  have hc : ((996053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((642949223341/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((996053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c16 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((672019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2084661/10000000) (δ := 10541/1000000000) (ψ := 73017/125000) 209 92
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t16 : ((671969/4000000 : ℚ) : ℝ) ≤ stT209 16 := by
  have hc : ((671969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671969/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((671969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c17 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((295687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18321/78125) (δ := 10527/1000000000) (ψ := 73017/125000) 209 94
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t17 : ((89635700709/625000000000 : ℚ) : ℝ) ≤ stT209 17 := by
  have hc : ((147831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89635700709/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((147831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c18 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((474967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 397213/5000000) (δ := 10591/1000000000) (ψ := 73017/125000) 209 96
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t18 : ((279862185681/1250000000000 : ℚ) : ℝ) ≤ stT209 18 := by
  have hc : ((237471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279862185681/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((237471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c19 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((582857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2371389/10000000) (δ := 5249/500000000) (ψ := 73017/125000) 209 98
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t19 : ((1337050758699/10000000000000 : ℚ) : ℝ) ≤ stT209 19 := by
  have hc : ((582807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1337050758699/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((582807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c20 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-940409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3493283/5000000) (δ := 10519/1000000000) (ψ := 73017/125000) 209 100
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t20 : ((-525732568803/2500000000000 : ℚ) : ℝ) ≤ stT209 20 := by
  have hc : ((-940459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-525732568803/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-940459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c21 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((109069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55967/200000) (δ := 2619/250000000) (ψ := 73017/125000) 209 101
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t21 : ((237980695057/2500000000000 : ℚ) : ℝ) ≤ stT209 21 := by
  have hc : ((218113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237980695057/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((218113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c22 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-152951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1077719/2500000) (δ := 10641/1000000000) (ψ := 73017/125000) 209 103
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t22 : ((-40774919501/1250000000000 : ℚ) : ℝ) ≤ stT209 22 := by
  have hc : ((-153001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40774919501/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-153001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c23 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((56789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603613/5000000) (δ := 2637/250000000) (ψ := 73017/125000) 209 104
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t23 : ((14799048897/250000000000 : ℚ) : ℝ) ≤ stT209 23 := by
  have hc : ((56779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14799048897/250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((56779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c24 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-364797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -597131/1000000) (δ := 527/50000000) (ψ := 73017/125000) 209 106
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t24 : ((-186172497231/1250000000000 : ℚ) : ℝ) ≤ stT209 24 := by
  have hc : ((-182411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186172497231/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-182411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c25 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((247557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174889/5000000) (δ := 1047/100000000) (ψ := 73017/125000) 209 107
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t25 : ((495089/2500000 : ℚ) : ℝ) ≤ stT209 25 := by
  have hc : ((495089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((495089/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((495089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c26 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-201837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2217537/5000000) (δ := 5313/500000000) (ψ := 73017/125000) 209 108
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t26 : ((-197966556347/5000000000000 : ℚ) : ℝ) ≤ stT209 26 := by
  have hc : ((-201887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197966556347/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-201887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c27 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-972053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1452309/2000000) (δ := 10591/1000000000) (ψ := 73017/125000) 209 110
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t27 : ((-1870813195603/10000000000000 : ℚ) : ℝ) ≤ stT209 27 := by
  have hc : ((-972103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1870813195603/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-972103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c28 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-16157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -793477/2000000) (δ := 5299/500000000) (ψ := 73017/125000) 209 111
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t28 : ((-30628361361/10000000000000 : ℚ) : ℝ) ≤ stT209 28 := by
  have hc : ((-16207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30628361361/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-16207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c29 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((859729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83759/625000) (δ := 5303/500000000) (ψ := 73017/125000) 209 112
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t29 : ((1596383498087/10000000000000 : ℚ) : ℝ) ≤ stT209 29 := by
  have hc : ((859679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1596383498087/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((859679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c30 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((192957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332713/5000000) (δ := 1049/100000000) (ψ := 73017/125000) 209 113
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t30 : ((352271248727/2000000000000 : ℚ) : ℝ) ≤ stT209 30 := by
  have hc : ((192947/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352271248727/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((192947/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c31 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((670381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1045093/5000000) (δ := 531/50000000) (ψ := 73017/125000) 209 114
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t31 : ((1203950003543/10000000000000 : ℚ) : ℝ) ≤ stT209 31 := by
  have hc : ((670331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1203950003543/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((670331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c32 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((14927/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1485459/5000000) (δ := 2619/250000000) (ψ := 73017/125000) 209 115
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t32 : ((527678151/8000000000 : ℚ) : ℝ) ≤ stT209 32 := by
  have hc : ((597/1600 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527678151/8000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((597/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c33 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((232211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835279/2500000) (δ := 5267/500000000) (ψ := 73017/125000) 209 116
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t33 : ((50517537117/1250000000000 : ℚ) : ℝ) ≤ stT209 33 := by
  have hc : ((232161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50517537117/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((232161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c34 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((274681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646269/2000000) (δ := 10461/1000000000) (ψ := 73017/125000) 209 117
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t34 : ((94197609107/2000000000000 : ℚ) : ℝ) ≤ stT209 34 := by
  have hc : ((274631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94197609107/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((274631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c35 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((96421/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2669351/10000000) (δ := 10649/1000000000) (ψ := 73017/125000) 209 118
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t35 : ((40741071147/500000000000 : ℚ) : ℝ) ≤ stT209 35 := by
  have hc : ((96411/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40741071147/500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((96411/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c36 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((97801/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 840341/5000000) (δ := 10647/1000000000) (ψ := 73017/125000) 209 119
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t36 : ((325982369607/2500000000000 : ℚ) : ℝ) ≤ stT209 36 := by
  have hc : ((391179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325982369607/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((391179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c37 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((49667/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288697/10000000) (δ := 10563/1000000000) (ψ := 73017/125000) 209 120
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t37 : ((163295783381/1000000000000 : ℚ) : ℝ) ≤ stT209 37 := by
  have hc : ((99329/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163295783381/1000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((99329/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c38 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((828679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371283/2500000) (δ := 1047/100000000) (ψ := 73017/125000) 209 121
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t38 : ((672106782303/5000000000000 : ℚ) : ℝ) ≤ stT209 38 := by
  have hc : ((828629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((672106782303/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((828629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c39 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((30533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3620897/10000000) (δ := 5313/500000000) (ψ := 73017/125000) 209 122
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t39 : ((97743793521/5000000000000 : ℚ) : ℝ) ≤ stT209 39 := by
  have hc : ((61041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97743793521/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((61041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c40 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-152779/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6100309/10000000) (δ := 2117/200000000) (ψ := 73017/125000) 209 123
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t40 : ((-241580646671/2000000000000 : ℚ) : ℝ) ≤ stT209 40 := by
  have hc : ((-152789/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241580646671/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-152789/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c41 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-114087/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3400787/5000000) (δ := 5259/500000000) (ψ := 73017/125000) 209 123
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t41 : ((-356367528137/2500000000000 : ℚ) : ℝ) ≤ stT209 41 := by
  have hc : ((-456373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356367528137/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-456373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c42 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((48401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3684607/10000000) (δ := 2623/250000000) (ψ := 73017/125000) 209 124
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t42 : ((9330720551/625000000000 : ℚ) : ℝ) ≤ stT209 42 := by
  have hc : ((6047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9330720551/625000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((6047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c43 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((248529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27133/1000000) (δ := 10499/1000000000) (ψ := 73017/125000) 209 125
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t43 : ((151593573901/1000000000000 : ℚ) : ℝ) ≤ stT209 43 := by
  have hc : ((497033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151593573901/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((497033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c44 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((199599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171231/500000) (δ := 10597/1000000000) (ψ := 73017/125000) 209 126
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t44 : ((75207823061/2500000000000 : ℚ) : ℝ) ≤ stT209 44 := by
  have hc : ((199549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75207823061/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((199549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c45 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-982867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1478109/2000000) (δ := 1049/100000000) (ψ := 73017/125000) 209 127
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t45 : ((-183155770863/1250000000000 : ℚ) : ℝ) ≤ stT209 45 := by
  have hc : ((-982917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183155770863/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-982917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c46 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-66527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 409343/1000000) (δ := 1059/100000000) (ψ := 73017/125000) 209 127
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t46 : ((-4908123017/500000000000 : ℚ) : ℝ) ≤ stT209 46 := by
  have hc : ((-66577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4908123017/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-66577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c47 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((494311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -377491/10000000) (δ := 263/25000000) (ψ := 73017/125000) 209 128
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t47 : ((360494889807/2500000000000 : ℚ) : ℝ) ≤ stT209 47 := by
  have hc : ((247143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360494889807/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((247143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c48 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-89367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5085053/10000000) (δ := 419/40000000) (ψ := 73017/125000) 209 129
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t48 : ((-8062788547/125000000000 : ℚ) : ℝ) ≤ stT209 48 := by
  have hc : ((-89377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8062788547/125000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-89377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c49 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-323863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5688479/10000000) (δ := 419/40000000) (ψ := 73017/125000) 209 129
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t49 : ((-7229645749/78125000000 : ℚ) : ℝ) ≤ stT209 49 := by
  have hc : ((-20243/31250 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7229645749/78125000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-20243/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c50 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((977063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 536479/10000000) (δ := 2107/200000000) (ψ := 73017/125000) 209 130
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t50 : ((1381704485769/10000000000000 : ℚ) : ℝ) ≤ stT209 50 := by
  have hc : ((977013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1381704485769/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((977013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c51 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-351389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2412313/5000000) (δ := 10461/1000000000) (ψ := 73017/125000) 209 131
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t51 : ((-492113354359/10000000000000 : ℚ) : ℝ) ≤ stT209 51 := by
  have hc : ((-351439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492113354359/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-351439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c52 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-529267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5321331/10000000) (δ := 10561/1000000000) (ψ := 73017/125000) 209 131
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t52 : ((-734030879067/10000000000000 : ℚ) : ℝ) ≤ stT209 52 := by
  have hc : ((-529317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-734030879067/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-529317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c53 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((984973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -433947/10000000) (δ := 10649/1000000000) (ψ := 73017/125000) 209 132
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t53 : ((270579031483/2000000000000 : ℚ) : ℝ) ≤ stT209 53 := by
  have hc : ((984923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270579031483/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((984923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c54 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-415059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6375289/10000000) (δ := 10647/1000000000) (ψ := 73017/125000) 209 133
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t54 : ((-35303620597/312500000000 : ℚ) : ℝ) ≤ stT209 54 := by
  have hc : ((-103771/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35303620597/312500000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-103771/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c55 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((282069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 803029/2500000) (δ := 10547/1000000000) (ψ := 73017/125000) 209 133
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t55 : ((380274137581/10000000000000 : ℚ) : ℝ) ≤ stT209 55 := by
  have hc : ((282019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380274137581/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((282019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c56 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((165953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3081181/10000000) (δ := 10539/1000000000) (ψ := 73017/125000) 209 134
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t56 : ((13858161373/312500000000 : ℚ) : ℝ) ≤ stT209 56 := by
  have hc : ((20741/62500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13858161373/312500000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((20741/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c57 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-390401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 308343/500000) (δ := 10539/1000000000) (ψ := 73017/125000) 209 134
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t57 : ((-258566060529/2500000000000 : ℚ) : ℝ) ≤ stT209 57 := by
  have hc : ((-195213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258566060529/2500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-195213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c58 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((245891/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3546/78125) (δ := 1329/125000000) (ψ := 73017/125000) 209 135
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t58 : ((80713551681/625000000000 : ℚ) : ℝ) ≤ stT209 58 := by
  have hc : ((491757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80713551681/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((491757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c59 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-121127/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7230027/10000000) (δ := 421/40000000) (ψ := 73017/125000) 209 136
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t59 : ((-63080866737/500000000000 : ℚ) : ℝ) ≤ stT209 59 := by
  have hc : ((-484533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63080866737/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-484533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c60 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((813487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1551683/10000000) (δ := 5239/500000000) (ψ := 73017/125000) 209 136
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t60 : ((525071143189/5000000000000 : ℚ) : ℝ) ≤ stT209 60 := by
  have hc : ((813437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525071143189/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((813437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c61 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-29743/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5519721/10000000) (δ := 2097/200000000) (ψ := 73017/125000) 209 137
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t61 : ((-76170432179/1000000000000 : ℚ) : ℝ) ≤ stT209 61 := by
  have hc : ((-59491/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76170432179/1000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-59491/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c62 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((46393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297639/1000000) (δ := 5259/500000000) (ψ := 73017/125000) 209 137
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t62 : ((235644875547/5000000000000 : ℚ) : ℝ) ≤ stT209 62 := by
  have hc : ((185547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235644875547/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((185547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c63 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-35363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092841/2500000) (δ := 2623/250000000) (ψ := 73017/125000) 209 138
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t63 : ((-22282902993/1000000000000 : ℚ) : ℝ) ≤ stT209 63 := by
  have hc : ((-35373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22282902993/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-35373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c64 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((27943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3857123/10000000) (δ := 331/31250000) (ψ := 73017/125000) 209 138
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t64 : ((27893/8000000 : ℚ) : ℝ) ≤ stT209 64 := by
  have hc : ((27893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27893/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((27893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c65 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((70779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -468737/1250000) (δ := 10499/1000000000) (ψ := 73017/125000) 209 139
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t65 : ((87728502963/10000000000000 : ℚ) : ℝ) ≤ stT209 65 := by
  have hc : ((70729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87728502963/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((70729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c66 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-14983/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4227373/10000000) (δ := 10599/1000000000) (ψ := 73017/125000) 209 139
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t66 : ((-14760394131/1000000000000 : ℚ) : ℝ) ≤ stT209 66 := by
  have hc : ((-59957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14760394131/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-59957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c67 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((121183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452911/1250000) (δ := 41/3906250) (ψ := 73017/125000) 209 140
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t67 : ((73993729651/5000000000000 : ℚ) : ℝ) ≤ stT209 67 := by
  have hc : ((121133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73993729651/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((121133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c68 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-76171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058801/5000000) (δ := 10507/1000000000) (ψ := 73017/125000) 209 140
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t68 : ((-92431606059/10000000000000 : ℚ) : ℝ) ≤ stT209 68 := by
  have hc : ((-76221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92431606059/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-76221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c69 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-7099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495311/1250000) (δ := 5307/500000000) (ψ := 73017/125000) 209 141
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t69 : ((-2144072879/1250000000000 : ℚ) : ℝ) ≤ stT209 69 := by
  have hc : ((-1781/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2144072879/1250000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-1781/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c70 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((18501/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3555607/10000000) (δ := 10589/1000000000) (ψ := 73017/125000) 209 141
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t70 : ((22105443053/1250000000000 : ℚ) : ℝ) ≤ stT209 70 := by
  have hc : ((73979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22105443053/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((73979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c71 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-79961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2370451/5000000) (δ := 10621/1000000000) (ψ := 73017/125000) 209 142
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t71 : ((-94911110277/2500000000000 : ℚ) : ℝ) ≤ stT209 71 := by
  have hc : ((-159947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94911110277/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-159947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c72 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((25879/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2566939/10000000) (δ := 5291/500000000) (ψ := 73017/125000) 209 142
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t72 : ((60991479783/1000000000000 : ℚ) : ℝ) ≤ stT209 72 := by
  have hc : ((51753/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60991479783/1000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((51753/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c73 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-359657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237361/400000) (δ := 423/40000000) (ψ := 73017/125000) 209 143
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t73 : ((-52622016123/625000000000 : ℚ) : ℝ) ≤ stT209 73 := by
  have hc : ((-179841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52622016123/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-179841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c74 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((445793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1174901/10000000) (δ := 423/40000000) (ψ := 73017/125000) 209 143
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t74 : ((16193581299/156250000000 : ℚ) : ℝ) ≤ stT209 74 := by
  have hc : ((55721/62500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16193581299/156250000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((55721/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c75 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-991063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1879873/2500000) (δ := 2107/200000000) (ψ := 73017/125000) 209 144
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t75 : ((-1144439172213/10000000000000 : ℚ) : ℝ) ≤ stT209 75 := by
  have hc : ((-991113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1144439172213/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-991113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c76 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((194289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4791/80000) (δ := 2107/200000000) (ψ := 73017/125000) 209 144
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t76 : ((111426583381/1000000000000 : ℚ) : ℝ) ≤ stT209 76 := by
  have hc : ((194279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111426583381/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((194279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c77 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-199161/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6231297/10000000) (δ := 2617/250000000) (ψ := 73017/125000) 209 144
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t77 : ((-226979315641/2500000000000 : ℚ) : ℝ) ≤ stT209 77 := by
  have hc : ((-398347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226979315641/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-398347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c78 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((459063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34183/125000) (δ := 33/3125000) (ψ := 73017/125000) 209 145
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t78 : ((519729862601/10000000000000 : ℚ) : ℝ) ≤ stT209 78 := by
  have hc : ((459013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519729862601/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((459013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c79 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((2201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245093/625000) (δ := 10543/1000000000) (ψ := 73017/125000) 209 145
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t79 : ((2420062137/10000000000000 : ℚ) : ℝ) ≤ stT209 79 := by
  have hc : ((2151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2420062137/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((2151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c80 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-246191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1303513/2500000) (δ := 213/20000000) (ψ := 73017/125000) 209 146
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t80 : ((-17204866209/312500000000 : ℚ) : ℝ) ≤ stT209 80 := by
  have hc : ((-30777/62500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17204866209/312500000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-30777/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c81 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((218103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39897/312500) (δ := 211/20000000) (ψ := 73017/125000) 209 146
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t81 : ((484645507091/5000000000000 : ℚ) : ℝ) ≤ stT209 81 := by
  have hc : ((436181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484645507091/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((436181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c82 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-31181/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7687831/10000000) (δ := 10453/1000000000) (ψ := 73017/125000) 209 146
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t82 : ((-137741610759/1250000000000 : ℚ) : ℝ) ≤ stT209 82 := by
  have hc : ((-498921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137741610759/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-498921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c83 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((780907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1686701/10000000) (δ := 5273/500000000) (ψ := 73017/125000) 209 147
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t83 : ((428550719597/5000000000000 : ℚ) : ℝ) ≤ stT209 83 := by
  have hc : ((780857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428550719597/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((780857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c84 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-254701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2285419/5000000) (δ := 21057/1000000000) (ψ := 73017/125000) 209 147
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t84 : ((-27795626859/1000000000000 : ℚ) : ℝ) ≤ stT209 84 := by
  have hc : ((-254751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27795626859/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-254751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c85 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-399209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2476813/5000000) (δ := 10639/1000000000) (ψ := 73017/125000) 209 148
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t85 : ((-433057472127/10000000000000 : ℚ) : ℝ) ≤ stT209 85 := by
  have hc : ((-399259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433057472127/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-399259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c86 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((894711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 578767/5000000) (δ := 10639/1000000000) (ψ := 73017/125000) 209 148
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t86 : ((964737112147/10000000000000 : ℚ) : ℝ) ≤ stT209 86 := by
  have hc : ((894661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((964737112147/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((894661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c87 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-965783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1439621/2000000) (δ := 2641/250000000) (ψ := 73017/125000) 209 148
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t87 : ((-1035482115129/10000000000000 : ℚ) : ℝ) ≤ stT209 87 := by
  have hc : ((-965833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1035482115129/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-965833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c88 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((527327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2538363/10000000) (δ := 2633/250000000) (ψ := 73017/125000) 209 149
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t88 : ((562078863831/10000000000000 : ℚ) : ℝ) ≤ stT209 88 := by
  have hc : ((527277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((562078863831/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((527277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c89 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((27833/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1682813/5000000) (δ := 10471/1000000000) (ψ := 73017/125000) 209 149
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t89 : ((117985086079/5000000000000 : ℚ) : ℝ) ≤ stT209 89 := by
  have hc : ((111307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117985086079/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((111307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c90 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-214443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203259/312500) (δ := 5239/500000000) (ψ := 73017/125000) 209 150
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t90 : ((-452112082723/5000000000000 : ℚ) : ℝ) ≤ stT209 90 := by
  have hc : ((-428911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452112082723/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-428911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c91 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((191517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -730741/10000000) (δ := 10539/500000000) (ψ := 73017/125000) 209 150
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t91 : ((50188430997/500000000000 : ℚ) : ℝ) ≤ stT209 91 := by
  have hc : ((191507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50188430997/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((191507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c92 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-81749/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4979687/10000000) (δ := 421/40000000) (ψ := 73017/125000) 209 150
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t92 : ((-85239725907/2000000000000 : ℚ) : ℝ) ≤ stT209 92 := by
  have hc : ((-81759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85239725907/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-81759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c93 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-111219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5079581/10000000) (δ := 10517/1000000000) (ψ := 73017/125000) 209 151
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t93 : ((-28835431597/625000000000 : ℚ) : ℝ) ≤ stT209 93 := by
  have hc : ((-222463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28835431597/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-222463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c94 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((122421/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508713/10000000) (δ := 10617/1000000000) (ψ := 73017/125000) 209 151
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t94 : ((505044575439/5000000000000 : ℚ) : ℝ) ≤ stT209 94 := by
  have hc : ((489659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505044575439/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((489659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c95 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-373769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6037861/10000000) (δ := 5293/500000000) (ψ := 73017/125000) 209 151
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t95 : ((-191752397163/2500000000000 : ℚ) : ℝ) ≤ stT209 95 := by
  have hc : ((-186897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191752397163/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-186897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c96 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-108529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65607/156250) (δ := 10593/1000000000) (ψ := 73017/125000) 209 152
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t96 : ((-110818007559/10000000000000 : ℚ) : ℝ) ≤ stT209 96 := by
  have hc : ((-108579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110818007559/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-108579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c97 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((35363/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243143/2000000) (δ := 10593/1000000000) (ψ := 73017/125000) 209 152
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t97 : ((17951824953/200000000000 : ℚ) : ℝ) ≤ stT209 97 := by
  have hc : ((35361/40000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17951824953/200000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((35361/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c98 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-435957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410921/625000) (δ := 10493/1000000000) (ψ := 73017/125000) 209 152
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t98 : ((-220204262623/2500000000000 : ℚ) : ℝ) ≤ stT209 98 := by
  have hc : ((-217991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220204262623/2500000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-217991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c99 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((39347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1914299/5000000) (δ := 53/5000000) (ψ := 73017/125000) 209 153
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t99 : ((39494938989/10000000000000 : ℚ) : ℝ) ≤ stT209 99 := by
  have hc : ((39297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39494938989/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((39297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c100 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((842401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1422683/10000000) (δ := 10603/1000000000) (ψ := 73017/125000) 209 153
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t100 : ((842350157649/10000000000000 : ℚ) : ℝ) ≤ stT209 100 := by
  have hc : ((842351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((842350157649/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((842351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c101 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-880971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6621767/10000000) (δ := 10603/1000000000) (ψ := 73017/125000) 209 153
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t101 : ((-438324686899/5000000000000 : ℚ) : ℝ) ≤ stT209 101 := by
  have hc : ((-881021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438324686899/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-881021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c102 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-4551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3938369/10000000) (δ := 10507/1000000000) (ψ := 73017/125000) 209 154
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t102 : ((-1138917737/2500000000000 : ℚ) : ℝ) ≤ stT209 102 := by
  have hc : ((-4601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1138917737/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-4601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c103 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((447207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1159193/10000000) (δ := 41/3906250) (ψ := 73017/125000) 209 154
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t103 : ((220310696439/2500000000000 : ℚ) : ℝ) ≤ stT209 103 := by
  have hc : ((223591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220310696439/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((223591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c104 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-790863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387971/625000) (δ := 10507/1000000000) (ψ := 73017/125000) 209 154
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t104 : ((-775554260453/10000000000000 : ℚ) : ℝ) ≤ stT209 104 := by
  have hc : ((-790913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-775554260453/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-790913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c105 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-14209/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1125091/2500000) (δ := 10589/1000000000) (ψ := 73017/125000) 209 155
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t105 : ((-110957015997/5000000000000 : ℚ) : ℝ) ≤ stT209 105 := by
  have hc : ((-113697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110957015997/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-113697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c106 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((491841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452257/10000000) (δ := 10489/1000000000) (ψ := 73017/125000) 209 155
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t106 : ((11942337589/125000000000 : ℚ) : ℝ) ≤ stT209 106 := by
  have hc : ((61477/62500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11942337589/125000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((61477/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c107 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-270899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1339607/2500000) (δ := 5307/500000000) (ψ := 73017/125000) 209 155
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t107 : ((-65478063747/1250000000000 : ℚ) : ℝ) ≤ stT209 107 := by
  have hc : ((-67731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65478063747/1250000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-67731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c108 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-146237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686129/1250000) (δ := 10581/1000000000) (ψ := 73017/125000) 209 156
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t108 : ((-281457455249/5000000000000 : ℚ) : ℝ) ≤ stT209 108 := by
  have hc : ((-292499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281457455249/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-292499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c109 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((481973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336679/5000000) (δ := 5261/500000000) (ψ := 73017/125000) 209 156
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t109 : ((57702790631/625000000000 : ℚ) : ℝ) ≤ stT209 109 := by
  have hc : ((120487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57702790631/625000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((120487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c110 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-68499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4098373/10000000) (δ := 10481/1000000000) (ψ := 73017/125000) 209 156
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t110 : ((-65358935187/10000000000000 : ℚ) : ℝ) ≤ stT209 110 := by
  have hc : ((-68549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65358935187/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-68549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c111 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-462609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6881017/10000000) (δ := 10629/1000000000) (ψ := 73017/125000) 209 157
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t111 : ((-109778190543/1250000000000 : ℚ) : ℝ) ≤ stT209 111 := by
  have hc : ((-231317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109778190543/1250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-231317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c112 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((127743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -548731/2500000) (δ := 5237/500000000) (ψ := 73017/125000) 209 157
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t112 : ((120696316763/2000000000000 : ℚ) : ℝ) ≤ stT209 112 := by
  have hc : ((127733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120696316763/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((127733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c113 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((278581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2449579/10000000) (δ := 10629/1000000000) (ψ := 73017/125000) 209 157
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t113 : ((818885001/15625000000 : ℚ) : ℝ) ≤ stT209 113 := by
  have hc : ((69639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((818885001/15625000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((69639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c114 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-949127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7053117/10000000) (δ := 5237/500000000) (ψ := 73017/125000) 209 157
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t114 : ((-444492944861/5000000000000 : ℚ) : ℝ) ≤ stT209 114 := by
  have hc : ((-949177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444492944861/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-949177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c115 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-65751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127859/312500) (δ := 10467/1000000000) (ψ := 73017/125000) 209 158
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t115 : ((-12271952301/2000000000000 : ℚ) : ℝ) ≤ stT209 115 := by
  have hc : ((-65801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12271952301/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-65801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c116 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((197017/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432317/10000000) (δ := 10467/1000000000) (ψ := 73017/125000) 209 158
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t116 : ((45729067833/500000000000 : ℚ) : ℝ) ≤ stT209 116 := by
  have hc : ((197007/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45729067833/500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((197007/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c117 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-77173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4917353/10000000) (δ := 2659/250000000) (ψ := 73017/125000) 209 158
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t117 : ((-71355760683/2000000000000 : ℚ) : ℝ) ≤ stT209 117 := by
  have hc : ((-77183/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71355760683/2000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-77183/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c118 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-411511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -634377/1000000) (δ := 523/50000000) (ψ := 73017/125000) 209 159
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t118 : ((-947124383/12500000000 : ℚ) : ℝ) ≤ stT209 118 := by
  have hc : ((-25721/31250 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-947124383/12500000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-25721/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c119 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((715261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1934497/10000000) (δ := 523/50000000) (ψ := 73017/125000) 209 159
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t119 : ((327816246639/5000000000000 : ℚ) : ℝ) ≤ stT209 119 := by
  have hc : ((715211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327816246639/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((715211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c120 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((280511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121897/500000) (δ := 10543/1000000000) (ψ := 73017/125000) 209 159
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t120 : ((12802362741/250000000000 : ℚ) : ℝ) ≤ stT209 120 := by
  have hc : ((140243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12802362741/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((140243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c121 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-56759/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6774063/10000000) (δ := 10543/1000000000) (ψ := 73017/125000) 209 159
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t121 : ((-412815495827/5000000000000 : ℚ) : ℝ) ≤ stT209 121 := by
  have hc : ((-454097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-412815495827/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-454097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c122 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-278843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579183/1250000) (δ := 211/20000000) (ψ := 73017/125000) 209 160
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t122 : ((-126249004347/5000000000000 : ℚ) : ℝ) ≤ stT209 122 := by
  have hc : ((-278893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126249004347/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-278893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c123 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((989177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18407/500000) (δ := 10453/1000000000) (ψ := 73017/125000) 209 160
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t123 : ((891865152963/10000000000000 : ℚ) : ℝ) ≤ stT209 123 := by
  have hc : ((989127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((891865152963/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((989127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c124 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((5147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3862647/10000000) (δ := 10453/1000000000) (ψ := 73017/125000) 209 160
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t124 : ((2306579781/1000000000000 : ℚ) : ℝ) ≤ stT209 124 := by
  have hc : ((5137/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2306579781/1000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((5137/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c125 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-62289/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1912123/2500000) (δ := 5273/500000000) (ψ := 73017/125000) 209 161
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t125 : ((-111431641559/1250000000000 : ℚ) : ℝ) ≤ stT209 125 := by
  have hc : ((-498337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111431641559/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-498337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c126 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((35167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3485107/10000000) (δ := 10557/1000000000) (ψ := 73017/125000) 209 161
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t126 : ((3132031659/200000000000 : ℚ) : ℝ) ≤ stT209 126 := by
  have hc : ((35157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3132031659/200000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((35157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c127 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((966871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645307/10000000) (δ := 5323/500000000) (ψ := 73017/125000) 209 161
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t127 : ((214478603819/2500000000000 : ℚ) : ℝ) ≤ stT209 127 := by
  have hc : ((966821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214478603819/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((966821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c128 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-160391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4743379/10000000) (δ := 5323/500000000) (ψ := 73017/125000) 209 161
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t128 : ((-1107727623/39062500000 : ℚ) : ℝ) ≤ stT209 128 := by
  have hc : ((-5013/15625 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1107727623/39062500000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-5013/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c129 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-115979/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -431149/625000) (δ := 2113/200000000) (ψ := 73017/125000) 209 162
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t129 : ((-408477317391/5000000000000 : ℚ) : ℝ) ≤ stT209 129 := by
  have hc : ((-463941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408477317391/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-463941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c130 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((412631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2863639/10000000) (δ := 2113/200000000) (ψ := 73017/125000) 209 162
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t130 : ((180928733349/5000000000000 : ℚ) : ℝ) ≤ stT209 130 := by
  have hc : ((412581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180928733349/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((412581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c131 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((897781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 570113/5000000) (δ := 2093/200000000) (ψ := 73017/125000) 209 162
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t131 : ((98043895703/1250000000000 : ℚ) : ℝ) ≤ stT209 131 := by
  have hc : ((897731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98043895703/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((897731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c132 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-57129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5113629/10000000) (δ := 5319/500000000) (ψ := 73017/125000) 209 162
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t132 : ((-198919572449/5000000000000 : ℚ) : ℝ) ≤ stT209 132 := by
  have hc : ((-228541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198919572449/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-228541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c133 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-886429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3325461/5000000) (δ := 10531/1000000000) (ψ := 73017/125000) 209 163
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t133 : ((-76867480569/1000000000000 : ℚ) : ℝ) ≤ stT209 133 := by
  have hc : ((-886479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76867480569/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-886479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c134 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((114551/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2737057/10000000) (δ := 5243/250000000) (ψ := 73017/125000) 209 163
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t134 : ((49473072459/1250000000000 : ℚ) : ℝ) ≤ stT209 134 := by
  have hc : ((229077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49473072459/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((229077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c135 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((44823/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143463/1250000) (δ := 10531/1000000000) (ψ := 73017/125000) 209 163
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t135 : ((38575301171/500000000000 : ℚ) : ℝ) ≤ stT209 135 := by
  have hc : ((89641/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38575301171/500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((89641/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c136 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-417531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2501903/5000000) (δ := 10631/1000000000) (ψ := 73017/125000) 209 163
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t136 : ((-358072784433/10000000000000 : ℚ) : ℝ) ≤ stT209 136 := by
  have hc : ((-417581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358072784433/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-417581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c137 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-57781/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -687627/1000000) (δ := 83/7812500) (ψ := 73017/125000) 209 164
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t137 : ((-197473317867/2500000000000 : ℚ) : ℝ) ≤ stT209 137 := by
  have hc : ((-462273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197473317867/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-462273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c138 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((166877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769071/2500000) (δ := 2631/250000000) (ψ := 73017/125000) 209 164
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t138 : ((4438555191/156250000000 : ℚ) : ℝ) ≤ stT209 138 := by
  have hc : ((41713/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4438555191/156250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((41713/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c139 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((961461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 696323/10000000) (δ := 10479/1000000000) (ψ := 73017/125000) 209 164
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t139 : ((203864318317/2500000000000 : ℚ) : ℝ) ≤ stT209 139 := by
  have hc : ((961411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203864318317/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((961411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c140 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-12781/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555233/1250000) (δ := 2631/250000000) (ψ := 73017/125000) 209 164
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t140 : ((-17287307463/1000000000000 : ℚ) : ℝ) ≤ stT209 140 := by
  have hc : ((-102273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17287307463/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-102273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c141 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-992483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3773629/5000000) (δ := 10617/1000000000) (ψ := 73017/125000) 209 165
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t141 : ((-104482956377/1250000000000 : ℚ) : ℝ) ≤ stT209 141 := by
  have hc : ((-992533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104482956377/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-992533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c142 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((14467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1927323/5000000) (δ := 10617/1000000000) (ψ := 73017/125000) 209 165
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t142 : ((6059726001/2500000000000 : ℚ) : ℝ) ≤ stT209 142 := by
  have hc : ((7221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6059726001/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((7221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c143 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((39887/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3759/200000) (δ := 10617/1000000000) (ψ := 73017/125000) 209 165
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t143 : ((3335351217/40000000000 : ℚ) : ℝ) ≤ stT209 143 := by
  have hc : ((7977/8000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3335351217/40000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((7977/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c144 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((94203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 431643/1250000) (δ := 5243/500000000) (ψ := 73017/125000) 209 165
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t144 : ((39240817637/2500000000000 : ℚ) : ℝ) ≤ stT209 144 := by
  have hc : ((47089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39240817637/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((47089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c145 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-951121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1413821/2000000) (δ := 10517/1000000000) (ψ := 73017/125000) 209 165
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t145 : ((-157980942561/2000000000000 : ℚ) : ℝ) ≤ stT209 145 := by
  have hc : ((-951171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157980942561/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-951171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c146 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-108361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -630971/1250000) (δ := 1051/100000000) (ψ := 73017/125000) 209 166
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t146 : ((-89690558841/2500000000000 : ℚ) : ℝ) ≤ stT209 146 := by
  have hc : ((-216747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89690558841/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-216747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c147 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((829551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296247/2000000) (δ := 10493/1000000000) (ψ := 73017/125000) 209 166
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t147 : ((342080405893/5000000000000 : ℚ) : ℝ) ≤ stT209 147 := by
  have hc : ((829501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342080405893/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((829501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c148 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((678951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1030579/5000000) (δ := 1051/100000000) (ψ := 73017/125000) 209 166
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t148 : ((279026274297/5000000000000 : ℚ) : ℝ) ≤ stT209 148 := by
  have hc : ((678901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279026274297/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((678901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c149 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-30699/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223189/400000) (δ := 1061/100000000) (ψ := 73017/125000) 209 166
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t149 : ((-1571978203/31250000000 : ℚ) : ℝ) ≤ stT209 149 := by
  have hc : ((-61403/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1571978203/31250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-61403/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c150 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-441571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -829161/1250000) (δ := 10603/1000000000) (ψ := 73017/125000) 209 167
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t150 : ((-90140452303/1250000000000 : ℚ) : ℝ) ≤ stT209 150 := by
  have hc : ((-110399/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90140452303/1250000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-110399/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c151 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((942/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -790371/2500000) (δ := 21/2000000) (ψ := 73017/125000) 209 167
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t151 : ((6131689133/250000000000 : ℚ) : ℝ) ≤ stT209 151 := by
  have hc : ((30139/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6131689133/250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((30139/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c152 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((4967/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143691/5000000) (δ := 53/5000000) (ψ := 73017/125000) 209 167
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t152 : ((16114262769/200000000000 : ℚ) : ℝ) ≤ stT209 152 := by
  have hc : ((19867/20000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16114262769/200000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((19867/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c153 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((21311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3713623/10000000) (δ := 10503/1000000000) (ψ := 73017/125000) 209 167
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t153 : ((8609407461/1250000000000 : ℚ) : ℝ) ≤ stT209 153 := by
  have hc : ((42597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8609407461/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((42597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c154 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-956927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3558777/5000000) (δ := 21/2000000) (ψ := 73017/125000) 209 167
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t154 : ((-771154077071/10000000000000 : ℚ) : ℝ) ≤ stT209 154 := by
  have hc : ((-956977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-771154077071/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-956977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c155 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-245229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325533/625000) (δ := 2627/250000000) (ψ := 73017/125000) 209 168
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t155 : ((-4924822947/125000000000 : ℚ) : ℝ) ≤ stT209 155 := by
  have hc : ((-122627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4924822947/125000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-122627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c156 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((147781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1848383/10000000) (δ := 2099/200000000) (ψ := 73017/125000) 209 168
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t156 : ((184861521/3125000000 : ℚ) : ℝ) ≤ stT209 156 := by
  have hc : ((147771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184861521/3125000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((147771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c157 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((827523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93143/625000) (δ := 663/62500000) (ψ := 73017/125000) 209 168
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t157 : ((330197308339/5000000000000 : ℚ) : ℝ) ≤ stT209 157 := by
  have hc : ((827473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330197308339/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((827473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c158 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-345059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 961549/2000000) (δ := 663/62500000) (ψ := 73017/125000) 209 168
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t158 : ((-137277112911/5000000000000 : ℚ) : ℝ) ≤ stT209 158 := by
  have hc : ((-345109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137277112911/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-345109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c159 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-994991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3801831/5000000) (δ := 2647/250000000) (ψ := 73017/125000) 209 169
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t159 : ((-197279813783/2500000000000 : ℚ) : ℝ) ≤ stT209 159 := by
  have hc : ((-995041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197279813783/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-995041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c160 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-39909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1081949/2500000) (δ := 2647/250000000) (ψ := 73017/125000) 209 169
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t160 : ((-6312148051/500000000000 : ℚ) : ℝ) ≤ stT209 160 := by
  have hc : ((-79843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6312148051/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-79843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c161 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((454703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1072359/10000000) (δ := 2123/200000000) (ψ := 73017/125000) 209 169
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t161 : ((17916813929/250000000000 : ℚ) : ℝ) ≤ stT209 161 := by
  have hc : ((227339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17916813929/250000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((227339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c162 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((1297/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2162961/10000000) (δ := 2123/200000000) (ψ := 73017/125000) 209 169
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t162 : ((5094703053/100000000000 : ℚ) : ℝ) ≤ stT209 162 := by
  have hc : ((12969/20000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5094703053/100000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((12969/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c163 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-274243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5378373/10000000) (δ := 2647/250000000) (ψ := 73017/125000) 209 169
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t163 : ((-53705856987/1250000000000 : ℚ) : ℝ) ≤ stT209 163 := by
  have hc : ((-68567/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53705856987/1250000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-68567/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c164 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-479401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57071/80000) (δ := 5311/500000000) (ψ := 73017/125000) 209 170
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t164 : ((-187184450597/2500000000000 : ℚ) : ℝ) ≤ stT209 164 := by
  have hc : ((-239713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187184450597/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-239713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c165 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-12243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1978799/5000000) (δ := 10481/1000000000) (ψ := 73017/125000) 209 170
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t165 : ((-9570088207/10000000000000 : ℚ) : ℝ) ≤ stT209 165 := by
  have hc : ((-12293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9570088207/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-12293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c166 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((949173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50031/625000) (δ := 5261/500000000) (ψ := 73017/125000) 209 170
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t166 : ((14733236329/200000000000 : ℚ) : ℝ) ≤ stT209 166 := by
  have hc : ((949123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14733236329/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((949123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c167 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((593757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2337691/10000000) (δ := 10481/1000000000) (ψ := 73017/125000) 209 170
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t167 : ((459424131861/10000000000000 : ℚ) : ℝ) ≤ stT209 167 := by
  have hc : ((593707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459424131861/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((593707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c168 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-574531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1364267/2500000) (δ := 10581/1000000000) (ψ := 73017/125000) 209 170
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t168 : ((-443299009377/10000000000000 : ℚ) : ℝ) ≤ stT209 168 := by
  have hc : ((-574581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-443299009377/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-574581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c169 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-96061/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3574981/5000000) (δ := 5237/500000000) (ψ := 73017/125000) 209 171
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t169 : ((-36948472623/500000000000 : ℚ) : ℝ) ≤ stT209 169 := by
  have hc : ((-48033/50000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36948472623/500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-48033/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c170 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-28061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4067369/10000000) (δ := 5287/500000000) (ψ := 73017/125000) 209 171
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t170 : ((-2154097899/500000000000 : ℚ) : ℝ) ≤ stT209 170 := by
  have hc : ((-14043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2154097899/500000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-14043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c171 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((115077/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501427/5000000) (δ := 5237/500000000) (ψ := 73017/125000) 209 171
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t171 : ((351987155477/5000000000000 : ℚ) : ℝ) ≤ stT209 171 := by
  have hc : ((460283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351987155477/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((460283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c172 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((136807/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2043791/10000000) (δ := 5287/500000000) (ψ := 73017/125000) 209 171
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t172 : ((26076654531/500000000000 : ℚ) : ℝ) ≤ stT209 172 := by
  have hc : ((136797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26076654531/500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((136797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c173 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-442437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 634097/1250000) (δ := 5237/500000000) (ψ := 73017/125000) 209 171
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t173 : ((-168208335641/5000000000000 : ℚ) : ℝ) ≤ stT209 173 := by
  have hc : ((-442487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168208335641/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-442487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c174 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-995759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3811827/5000000) (δ := 10467/1000000000) (ψ := 73017/125000) 209 172
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t174 : ((-754921807091/10000000000000 : ℚ) : ℝ) ≤ stT209 174 := by
  have hc : ((-995809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-754921807091/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-995809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c175 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-277267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4629363/10000000) (δ := 1317/125000000) (ψ := 73017/125000) 209 172
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t175 : ((-209631962493/10000000000000 : ℚ) : ℝ) ≤ stT209 175 := by
  have hc : ((-277317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209631962493/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-277317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c176 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((789463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826079/5000000) (δ := 1317/125000000) (ψ := 73017/125000) 209 172
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t176 : ((297521076157/5000000000000 : ℚ) : ℝ) ≤ stT209 176 := by
  have hc : ((789413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297521076157/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((789413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c177 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((43309/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654111/5000000) (δ := 10567/1000000000) (ψ := 73017/125000) 209 172
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t177 : ((32551157499/500000000000 : ℚ) : ℝ) ≤ stT209 177 := by
  have hc : ((86613/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32551157499/500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((86613/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c178 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-129591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4251883/10000000) (δ := 1317/125000000) (ψ := 73017/125000) 209 172
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t178 : ((-24292519503/2500000000000 : ℚ) : ℝ) ≤ stT209 178 := by
  have hc : ((-129641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24292519503/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-129641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c179 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-481891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1435817/2000000) (δ := 2659/250000000) (ψ := 73017/125000) 209 172
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t179 : ((-22512585461/312500000000 : ℚ) : ℝ) ≤ stT209 179 := by
  have hc : ((-120479/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22512585461/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-120479/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c180 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-313001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5618031/10000000) (δ := 659/62500000) (ψ := 73017/125000) 209 173
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t180 : ((-29164475907/625000000000 : ℚ) : ℝ) ≤ stT209 180 := by
  have hc : ((-156513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29164475907/625000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-156513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c181 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((57887/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2723277/10000000) (δ := 10559/1000000000) (ψ := 73017/125000) 209 173
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t181 : ((86044828381/2500000000000 : ℚ) : ℝ) ≤ stT209 181 := by
  have hc : ((231523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86044828381/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((231523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c182 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((499033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155489/10000000) (δ := 10559/1000000000) (ψ := 73017/125000) 209 173
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t182 : ((5779518453/78125000000 : ℚ) : ℝ) ≤ stT209 182 := by
  have hc : ((15594/15625 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5779518453/78125000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((15594/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c183 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((4443/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94329/312500) (δ := 10459/1000000000) (ψ := 73017/125000) 209 173
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t183 : ((26271175119/1000000000000 : ℚ) : ℝ) ≤ stT209 183 := by
  have hc : ((35539/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26271175119/1000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((35539/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c184 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-700131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 733243/1250000) (δ := 10459/1000000000) (ψ := 73017/125000) 209 173
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t184 : ((-51618043501/1000000000000 : ℚ) : ℝ) ≤ stT209 184 := by
  have hc : ((-700181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51618043501/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-700181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c185 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-943557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7010017/10000000) (δ := 2613/250000000) (ψ := 73017/125000) 209 174
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t185 : ((-138750804101/2000000000000 : ℚ) : ℝ) ≤ stT209 185 := by
  have hc : ((-943607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138750804101/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-943607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c186 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-26583/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1048331/2500000) (δ := 2613/250000000) (ψ := 73017/125000) 209 174
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t186 : ((-9750389019/1250000000000 : ℚ) : ℝ) ≤ stT209 186 := by
  have hc : ((-53191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9750389019/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-53191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c187 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((424509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1391679/10000000) (δ := 2613/250000000) (ψ := 73017/125000) 209 174
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t187 : ((9700414489/156250000000 : ℚ) : ℝ) ≤ stT209 187 := by
  have hc : ((106121/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9700414489/156250000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((106121/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c188 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((424161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139497/1000000) (δ := 1319/125000000) (ψ := 73017/125000) 209 174
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t188 : ((9666642627/156250000000 : ℚ) : ℝ) ≤ stT209 188 := by
  have hc : ((53017/62500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9666642627/156250000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((53017/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c189 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-9581/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 833377/2000000) (δ := 2613/250000000) (ψ := 73017/125000) 209 174
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t189 : ((-3486394649/500000000000 : ℚ) : ℝ) ≤ stT209 189 := by
  have hc : ((-4793/50000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3486394649/500000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-4793/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c190 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-465811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3462059/5000000) (δ := 10651/1000000000) (ψ := 73017/125000) 209 174
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t190 : ((-84488325943/1250000000000 : ℚ) : ℝ) ≤ stT209 190 := by
  have hc : ((-116459/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84488325943/1250000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-116459/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c191 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-748381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3020517/5000000) (δ := 5279/500000000) (ψ := 73017/125000) 209 175
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t191 : ((-21661838433/400000000000 : ℚ) : ℝ) ≤ stT209 191 := by
  have hc : ((-748431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21661838433/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-748431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c192 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((243293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207037/625000) (δ := 2129/200000000) (ψ := 73017/125000) 209 175
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t192 : ((175545310941/10000000000000 : ℚ) : ℝ) ≤ stT209 192 := by
  have hc : ((243243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175545310941/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((243243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c193 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((971499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -598309/10000000) (δ := 2129/200000000) (ψ := 73017/125000) 209 175
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t193 : ((139852712387/2000000000000 : ℚ) : ℝ) ≤ stT209 193 := by
  have hc : ((971449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139852712387/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((971449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c194 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((166719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2101971/10000000) (δ := 2129/200000000) (ψ := 73017/125000) 209 175
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t194 : ((119688265327/2500000000000 : ℚ) : ℝ) ≤ stT209 194 := by
  have hc : ((333413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119688265327/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((333413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c195 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-42221/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4788353/10000000) (δ := 5229/500000000) (ψ := 73017/125000) 209 175
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t195 : ((-24191653707/1000000000000 : ℚ) : ℝ) ≤ stT209 195 := by
  have hc : ((-168909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24191653707/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-168909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c196 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-98767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7460993/10000000) (δ := 5279/500000000) (ψ := 73017/125000) 209 175
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t196 : ((-8818932099/125000000000 : ℚ) : ℝ) ≤ stT209 196 := by
  have hc : ((-24693/25000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8818932099/125000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-24693/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c197 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-616563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1396979/2500000) (δ := 5269/500000000) (ψ := 73017/125000) 209 176
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t197 : ((-439318880723/10000000000000 : ℚ) : ℝ) ≤ stT209 197 := by
  have hc : ((-616613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439318880723/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-616613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c198 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((76751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1471171/5000000) (δ := 5319/500000000) (ψ := 73017/125000) 209 176
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t198 : ((54537449729/2000000000000 : ℚ) : ℝ) ≤ stT209 198 := by
  have hc : ((76741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54537449729/2000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((76741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c199 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((992317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -310091/10000000) (δ := 2093/200000000) (ψ := 73017/125000) 209 176
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t199 : ((703399223227/10000000000000 : ℚ) : ℝ) ≤ stT209 199 := by
  have hc : ((992267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((703399223227/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((992267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c200 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((602971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115447/500000) (δ := 5269/500000000) (ψ := 73017/125000) 209 176
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t200 : ((213164528313/5000000000000 : ℚ) : ℝ) ≤ stT209 200 := by
  have hc : ((602921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213164528313/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((602921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c201 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-192491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4914961/10000000) (δ := 5269/500000000) (ψ := 73017/125000) 209 176
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t201 : ((-16973798817/625000000000 : ℚ) : ℝ) ≤ stT209 201 := by
  have hc : ((-48129/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16973798817/625000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-48129/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c202 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-990437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1876993/2500000) (δ := 2093/200000000) (ψ := 73017/125000) 209 176
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t202 : ((-348452336113/5000000000000 : ℚ) : ℝ) ≤ stT209 202 := by
  have hc : ((-990487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348452336113/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-990487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c203 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-156633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -561973/1000000) (δ := 10631/1000000000) (ψ := 73017/125000) 209 177
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t203 : ((-219887361133/5000000000000 : ℚ) : ℝ) ≤ stT209 203 := by
  have hc : ((-313291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219887361133/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-313291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c204 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((21427/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -610433/2000000) (δ := 10631/1000000000) (ψ := 73017/125000) 209 177
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t204 : ((5999884737/250000000000 : ℚ) : ℝ) ≤ stT209 204 := by
  have hc : ((171391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5999884737/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((171391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c205 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((980293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24857/500000) (δ := 10631/1000000000) (ψ := 73017/125000) 209 177
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t205 : ((68463111849/1000000000000 : ℚ) : ℝ) ≤ stT209 205 := by
  have hc : ((980243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68463111849/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((980243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c206 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((683551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40909/200000) (δ := 1309/125000000) (ψ := 73017/125000) 209 177
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t206 : ((476217702233/10000000000000 : ℚ) : ℝ) ≤ stT209 206 := by
  have hc : ((683501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476217702233/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((683501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c207 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-51317/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1143927/2500000) (δ := 10631/1000000000) (ψ := 73017/125000) 209 177
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t207 : ((-35674780023/2000000000000 : ℚ) : ℝ) ≤ stT209 207 := by
  have hc : ((-51327/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35674780023/2000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-51327/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c208 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-238531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7093793/10000000) (δ := 2643/250000000) (ψ := 73017/125000) 209 177
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t208 : ((-2584380279/39062500000 : ℚ) : ℝ) ≤ stT209 208 := by
  have hc : ((-477087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2584380279/39062500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-477087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c209 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-765917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1527039/2500000) (δ := 10479/1000000000) (ψ := 73017/125000) 209 178
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t209 : ((-105966172681/2000000000000 : ℚ) : ℝ) ≤ stT209 209 := by
  have hc : ((-765967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105966172681/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-765967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c210 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((124827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3614107/10000000) (δ := 2631/250000000) (ψ := 73017/125000) 209 178
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t210 : ((17220848101/2000000000000 : ℚ) : ℝ) ≤ stT209 210 := by
  have hc : ((124777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17220848101/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((124777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c211 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((22481/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -565959/5000000) (δ := 10579/1000000000) (ψ := 73017/125000) 209 178
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t211 : ((15475689333/250000000000 : ℚ) : ℝ) ≤ stT209 211 := by
  have hc : ((89919/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15475689333/250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((89919/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c212 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((430031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 669257/5000000) (δ := 10479/1000000000) (ψ := 73017/125000) 209 178
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t212 : ((73832245203/1250000000000 : ℚ) : ℝ) ≤ stT209 212 := by
  have hc : ((215003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73832245203/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((215003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c213 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((25917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3797347/10000000) (δ := 10579/1000000000) (ψ := 73017/125000) 209 178
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t213 : ((1108805481/312500000000 : ℚ) : ℝ) ≤ stT209 213 := by
  have hc : ((6473/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1108805481/312500000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((6473/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c214 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-799869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1561171/2500000) (δ := 83/7812500) (ψ := 73017/125000) 209 178
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t214 : ((-273406714767/5000000000000 : ℚ) : ℝ) ≤ stT209 214 := by
  have hc : ((-799919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273406714767/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-799919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c215 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-189167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -878423/1250000) (δ := 2629/250000000) (ψ := 73017/125000) 209 179
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t215 : ((-25803553623/400000000000 : ℚ) : ℝ) ≤ stT209 215 := by
  have hc : ((-189177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25803553623/400000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-189177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c216 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-133517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184111/400000) (δ := 2629/250000000) (ψ := 73017/125000) 209 179
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t216 : ((-22715961597/1250000000000 : ℚ) : ℝ) ≤ stT209 216 := by
  have hc : ((-66771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22715961597/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-66771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c217 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((640413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10947/50000) (δ := 1327/125000000) (ψ := 73017/125000) 209 179
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t217 : ((108676645093/2500000000000 : ℚ) : ℝ) ≤ stT209 217 := by
  have hc : ((640363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108676645093/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((640363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c218 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((124547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212899/10000000) (δ := 10587/1000000000) (ψ := 73017/125000) 209 179
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t218 : ((67479665491/1000000000000 : ℚ) : ℝ) ≤ stT209 218 := by
  have hc : ((498163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67479665491/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((498163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c219 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((252381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40691/156250) (δ := 1327/125000000) (ψ := 73017/125000) 209 179
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t219 : ((42631571593/1250000000000 : ℚ) : ℝ) ≤ stT209 219 := by
  have hc : ((63089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42631571593/1250000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((63089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c220 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-410549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498463/1000000) (δ := 10487/1000000000) (ψ := 73017/125000) 209 179
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t220 : ((-1384129229/50000000000 : ℚ) : ℝ) ≤ stT209 220 := by
  have hc : ((-410599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1384129229/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-410599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c221 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-98009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229821/312500) (δ := 10487/1000000000) (ψ := 73017/125000) 209 179
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t221 : ((-32965685711/500000000000 : ℚ) : ℝ) ≤ stT209 221 := by
  have hc : ((-49007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32965685711/500000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-49007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c222 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-735991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5994813/10000000) (δ := 10509/1000000000) (ψ := 73017/125000) 209 180
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t222 : ((-493999069437/10000000000000 : ℚ) : ℝ) ≤ stT209 222 := by
  have hc : ((-736041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493999069437/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-736041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c223 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((22393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3646489/10000000) (δ := 10509/1000000000) (ψ := 73017/125000) 209 180
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t223 : ((14988753567/2000000000000 : ℚ) : ℝ) ≤ stT209 223 := by
  have hc : ((22383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14988753567/2000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((22383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c224 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((866091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1308667/10000000) (δ := 5247/500000000) (ψ := 73017/125000) 209 180
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t224 : ((578647892273/10000000000000 : ℚ) : ℝ) ≤ stT209 224 := by
  have hc : ((866041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((578647892273/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((866041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c225 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((918113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1018757/10000000) (δ := 5247/500000000) (ψ := 73017/125000) 209 180
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t225 : ((306020693979/5000000000000 : ℚ) : ℝ) ≤ stT209 225 := by
  have hc : ((918063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306020693979/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((918063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c226 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((9371/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3335809/10000000) (δ := 21009/1000000000) (ψ := 73017/125000) 209 180
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t226 : ((623216511/40000000000 : ℚ) : ℝ) ≤ stT209 226 := by
  have hc : ((9369/40000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((623216511/40000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((9369/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c227 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-316829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5642673/10000000) (δ := 5247/500000000) (ψ := 73017/125000) 209 180
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t227 : ((-26287950537/625000000000 : ℚ) : ℝ) ≤ stT209 227 := by
  have hc : ((-158427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26287950537/625000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-158427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c228 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-999417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7768589/10000000) (δ := 10601/1000000000) (ψ := 73017/125000) 209 181
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t228 : ((-661914011689/10000000000000 : ℚ) : ℝ) ≤ stT209 228 := by
  have hc : ((-999467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661914011689/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-999467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c229 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-582639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17131/31250) (δ := 10601/1000000000) (ψ := 73017/125000) 209 181
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t229 : ((-385051962291/10000000000000 : ℚ) : ℝ) ≤ stT209 229 := by
  have hc : ((-582689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385051962291/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-582689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c230 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((28471/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3205231/10000000) (δ := 10501/1000000000) (ψ := 73017/125000) 209 181
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t230 : ((469247777/25000000000 : ℚ) : ℝ) ≤ stT209 230 := by
  have hc : ((14233/50000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469247777/25000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((14233/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c231 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((930373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -938417/10000000) (δ := 10501/1000000000) (ψ := 73017/125000) 209 181
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t231 : ((612106948173/10000000000000 : ℚ) : ℝ) ≤ stT209 231 := by
  have hc : ((930323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((612106948173/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((930323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c232 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((108013/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 659287/5000000) (δ := 10501/1000000000) (ψ := 73017/125000) 209 181
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t232 : ((70909887591/1250000000000 : ℚ) : ℝ) ≤ stT209 232 := by
  have hc : ((432027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70909887591/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((432027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c233 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((28787/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3565899/10000000) (δ := 10601/1000000000) (ψ := 73017/125000) 209 181
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t233 : ((18852417017/2000000000000 : ℚ) : ℝ) ≤ stT209 233 := by
  have hc : ((28777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18852417017/2000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((28777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c234 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-10658/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5803609/10000000) (δ := 5301/500000000) (ψ := 73017/125000) 209 181
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t234 : ((-222971812401/5000000000000 : ℚ) : ℝ) ≤ stT209 234 := by
  have hc : ((-341081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222971812401/5000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-341081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c235 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-997473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1535241/2000000) (δ := 2099/200000000) (ψ := 73017/125000) 209 182
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t235 : ((-650713181067/10000000000000 : ℚ) : ℝ) ≤ stT209 235 := by
  have hc : ((-997523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-650713181067/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-997523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c236 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-574677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5457513/10000000) (δ := 2627/250000000) (ψ := 73017/125000) 209 182
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t236 : ((-74823133403/2000000000000 : ℚ) : ℝ) ≤ stT209 236 := by
  have hc : ((-574727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74823133403/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-574727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c237 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((268183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1624113/5000000) (δ := 663/62500000) (ψ := 73017/125000) 209 182
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t237 : ((174170884677/10000000000000 : ℚ) : ℝ) ≤ stT209 237 := by
  have hc : ((268133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174170884677/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((268133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c238 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((28543/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13103/125000) (δ := 2627/250000000) (ψ := 73017/125000) 209 182
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t238 : ((296010326589/5000000000000 : ℚ) : ℝ) ≤ stT209 238 := by
  have hc : ((456663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296010326589/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((456663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c239 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((897371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22851/200000) (δ := 2099/200000000) (ψ := 73017/125000) 209 182
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t239 : ((290214249783/5000000000000 : ℚ) : ℝ) ≤ stT209 239 := by
  have hc : ((897321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290214249783/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((897321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c240 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((59697/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3324197/10000000) (δ := 663/62500000) (ψ := 73017/125000) 209 182
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t240 : ((77052331393/5000000000000 : ℚ) : ℝ) ≤ stT209 240 := by
  have hc : ((119369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77052331393/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((119369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c241 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-11749/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343547/625000) (δ := 663/62500000) (ψ := 73017/125000) 209 182
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t241 : ((-30275379/800000000 : ℚ) : ℝ) ≤ stT209 241 := by
  have hc : ((-47/80 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30275379/800000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-47/80 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c242 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-997001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47877/62500) (δ := 663/62500000) (ψ := 73017/125000) 209 182
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t242 : ((-25637172363/400000000000 : ℚ) : ℝ) ≤ stT209 242 := by
  have hc : ((-997051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25637172363/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-997051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c243 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-35391/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589301/1000000) (δ := 2123/200000000) (ψ := 73017/125000) 209 183
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t243 : ((-45409931287/1000000000000 : ℚ) : ℝ) ≤ stT209 243 := by
  have hc : ((-70787/100000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45409931287/1000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-70787/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c244 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((17963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3747207/10000000) (δ := 2123/200000000) (ψ := 73017/125000) 209 183
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t244 : ((2872905723/625000000000 : ℚ) : ℝ) ≤ stT209 244 := by
  have hc : ((35901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2872905723/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((35901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c245 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((15993/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1610209/10000000) (δ := 659/31250000) (ψ := 73017/125000) 209 183
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t245 : ((319278281/6250000000 : ℚ) : ℝ) ≤ stT209 245 := by
  have hc : ((1999/2500 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319278281/6250000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((1999/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c246 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((978601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518117/10000000) (δ := 2103/200000000) (ψ := 73017/125000) 209 183
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t246 : ((77987579047/1250000000000 : ℚ) : ℝ) ≤ stT209 246 := by
  have hc : ((978551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77987579047/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((978551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c247 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((789/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527559/2000000) (δ := 2103/200000000) (ψ := 73017/125000) 209 183
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t247 : ((3137357333/100000000000 : ℚ) : ℝ) ≤ stT209 247 := by
  have hc : ((19723/40000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3137357333/100000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((19723/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c248 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-2583/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 593613/1250000) (δ := 2103/200000000) (ψ := 73017/125000) 209 183
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t248 : ((-8202307917/400000000000 : ℚ) : ℝ) ≤ stT209 248 := by
  have hc : ((-12917/40000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8202307917/400000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-12917/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c249 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-920673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856437/1250000) (δ := 1311/125000000) (ψ := 73017/125000) 209 183
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t249 : ((-23339407327/400000000000 : ℚ) : ℝ) ≤ stT209 249 := by
  have hc : ((-920723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23339407327/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-920723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_c250 :
    |Real.cos (((209 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-906153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1352447/2000000) (δ := 131/12500000) (ψ := 73017/125000) 209 184
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st209_t250 : ((-71641690571/1250000000000 : ℚ) : ℝ) ≤ stT209 250 := by
  have hc : ((-906203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((209 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((73017/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st209_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71641690571/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-906203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st209_p1 : ((834139/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT209 (i+1) := by
  rw [Finset.sum_range_one]
  exact st209_t1

theorem st209_p2 : ((7613236897883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT209 (i+1))
      = (∑ i ∈ Finset.range 1, stT209 (i+1)) + stT209 2 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 1
    simpa using h
  have hprev := st209_p1
  have hstep := st209_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p3 : ((9728661337519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT209 (i+1))
      = (∑ i ∈ Finset.range 2, stT209 (i+1)) + stT209 3 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 2
    simpa using h
  have hprev := st209_p2
  have hstep := st209_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p4 : ((14689486337519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT209 (i+1))
      = (∑ i ∈ Finset.range 3, stT209 (i+1)) + stT209 4 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 3
    simpa using h
  have hprev := st209_p3
  have hstep := st209_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p5 : ((2101398539539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT209 (i+1))
      = (∑ i ∈ Finset.range 4, stT209 (i+1)) + stT209 5 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 4
    simpa using h
  have hprev := st209_p4
  have hstep := st209_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p6 : ((3214134832269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT209 (i+1))
      = (∑ i ∈ Finset.range 5, stT209 (i+1)) + stT209 6 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 5
    simpa using h
  have hprev := st209_p5
  have hstep := st209_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p7 : ((1960600449439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT209 (i+1))
      = (∑ i ∈ Finset.range 6, stT209 (i+1)) + stT209 7 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 6
    simpa using h
  have hprev := st209_p6
  have hstep := st209_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p8 : ((3529033598899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT209 (i+1))
      = (∑ i ∈ Finset.range 7, stT209 (i+1)) + stT209 8 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 7
    simpa using h
  have hprev := st209_p7
  have hstep := st209_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p9 : ((10388983531373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT209 (i+1))
      = (∑ i ∈ Finset.range 8, stT209 (i+1)) + stT209 9 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 8
    simpa using h
  have hprev := st209_p8
  have hstep := st209_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p10 : ((7226635961257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT209 (i+1))
      = (∑ i ∈ Finset.range 9, stT209 (i+1)) + stT209 10 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 9
    simpa using h
  have hprev := st209_p9
  have hstep := st209_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p11 : ((5759692546837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT209 (i+1))
      = (∑ i ∈ Finset.range 10, stT209 (i+1)) + stT209 11 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 10
    simpa using h
  have hprev := st209_p10
  have hstep := st209_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p12 : ((3099062717749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT209 (i+1))
      = (∑ i ∈ Finset.range 11, stT209 (i+1)) + stT209 12 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 11
    simpa using h
  have hprev := st209_p11
  have hstep := st209_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p13 : ((3516871078249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT209 (i+1))
      = (∑ i ∈ Finset.range 12, stT209 (i+1)) + stT209 13 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 12
    simpa using h
  have hprev := st209_p12
  have hstep := st209_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p14 : ((637158541999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT209 (i+1))
      = (∑ i ∈ Finset.range 13, stT209 (i+1)) + stT209 14 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 13
    simpa using h
  have hprev := st209_p13
  have hstep := st209_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p15 : ((64005388267/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT209 (i+1))
      = (∑ i ∈ Finset.range 14, stT209 (i+1)) + stT209 15 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 14
    simpa using h
  have hprev := st209_p14
  have hstep := st209_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p16 : ((85004419517/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT209 (i+1))
      = (∑ i ∈ Finset.range 15, stT209 (i+1)) + stT209 16 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 15
    simpa using h
  have hprev := st209_p15
  have hstep := st209_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p17 : ((257328899147/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT209 (i+1))
      = (∑ i ∈ Finset.range 16, stT209 (i+1)) + stT209 17 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 16
    simpa using h
  have hprev := st209_p16
  have hstep := st209_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p18 : ((1309177782269/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT209 (i+1))
      = (∑ i ∈ Finset.range 17, stT209 (i+1)) + stT209 18 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 17
    simpa using h
  have hprev := st209_p17
  have hstep := st209_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p19 : ((11810473016851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT209 (i+1))
      = (∑ i ∈ Finset.range 18, stT209 (i+1)) + stT209 19 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 18
    simpa using h
  have hprev := st209_p18
  have hstep := st209_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p20 : ((9707542741639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT209 (i+1))
      = (∑ i ∈ Finset.range 19, stT209 (i+1)) + stT209 20 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 19
    simpa using h
  have hprev := st209_p19
  have hstep := st209_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p21 : ((10659465521867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT209 (i+1))
      = (∑ i ∈ Finset.range 20, stT209 (i+1)) + stT209 21 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 20
    simpa using h
  have hprev := st209_p20
  have hstep := st209_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p22 : ((10333266165859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT209 (i+1))
      = (∑ i ∈ Finset.range 21, stT209 (i+1)) + stT209 22 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 21
    simpa using h
  have hprev := st209_p21
  have hstep := st209_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p23 : ((10925228121739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT209 (i+1))
      = (∑ i ∈ Finset.range 22, stT209 (i+1)) + stT209 23 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 22
    simpa using h
  have hprev := st209_p22
  have hstep := st209_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p24 : ((9435848143891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT209 (i+1))
      = (∑ i ∈ Finset.range 23, stT209 (i+1)) + stT209 24 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 23
    simpa using h
  have hprev := st209_p23
  have hstep := st209_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p25 : ((11416204143891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT209 (i+1))
      = (∑ i ∈ Finset.range 24, stT209 (i+1)) + stT209 25 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 24
    simpa using h
  have hprev := st209_p24
  have hstep := st209_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p26 : ((11020271031197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT209 (i+1))
      = (∑ i ∈ Finset.range 25, stT209 (i+1)) + stT209 26 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 25
    simpa using h
  have hprev := st209_p25
  have hstep := st209_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p27 : ((4574728917797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT209 (i+1))
      = (∑ i ∈ Finset.range 26, stT209 (i+1)) + stT209 27 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 26
    simpa using h
  have hprev := st209_p26
  have hstep := st209_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p28 : ((9118829474233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT209 (i+1))
      = (∑ i ∈ Finset.range 27, stT209 (i+1)) + stT209 28 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 27
    simpa using h
  have hprev := st209_p27
  have hstep := st209_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p29 : ((66970081077/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT209 (i+1))
      = (∑ i ∈ Finset.range 28, stT209 (i+1)) + stT209 29 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 28
    simpa using h
  have hprev := st209_p28
  have hstep := st209_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p30 : ((2495313843191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT209 (i+1))
      = (∑ i ∈ Finset.range 29, stT209 (i+1)) + stT209 30 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 29
    simpa using h
  have hprev := st209_p29
  have hstep := st209_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p31 : ((6840259609749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT209 (i+1))
      = (∑ i ∈ Finset.range 30, stT209 (i+1)) + stT209 31 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 30
    simpa using h
  have hprev := st209_p30
  have hstep := st209_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p32 : ((1792514613531/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT209 (i+1))
      = (∑ i ∈ Finset.range 31, stT209 (i+1)) + stT209 32 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 31
    simpa using h
  have hprev := st209_p31
  have hstep := st209_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p33 : ((230379018831/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT209 (i+1))
      = (∑ i ∈ Finset.range 32, stT209 (i+1)) + stT209 33 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 32
    simpa using h
  have hprev := st209_p32
  have hstep := st209_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p34 : ((15215245250719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT209 (i+1))
      = (∑ i ∈ Finset.range 33, stT209 (i+1)) + stT209 34 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 33
    simpa using h
  have hprev := st209_p33
  have hstep := st209_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p35 : ((16030066673659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT209 (i+1))
      = (∑ i ∈ Finset.range 34, stT209 (i+1)) + stT209 35 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 34
    simpa using h
  have hprev := st209_p34
  have hstep := st209_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p36 : ((17333996152087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT209 (i+1))
      = (∑ i ∈ Finset.range 35, stT209 (i+1)) + stT209 36 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 35
    simpa using h
  have hprev := st209_p35
  have hstep := st209_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p37 : ((18966953985897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT209 (i+1))
      = (∑ i ∈ Finset.range 36, stT209 (i+1)) + stT209 37 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 36
    simpa using h
  have hprev := st209_p36
  have hstep := st209_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p38 : ((20311167550503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT209 (i+1))
      = (∑ i ∈ Finset.range 37, stT209 (i+1)) + stT209 38 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 37
    simpa using h
  have hprev := st209_p37
  have hstep := st209_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p39 : ((4101331027509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT209 (i+1))
      = (∑ i ∈ Finset.range 38, stT209 (i+1)) + stT209 39 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 38
    simpa using h
  have hprev := st209_p38
  have hstep := st209_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p40 : ((1929875190419/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT209 (i+1))
      = (∑ i ∈ Finset.range 39, stT209 (i+1)) + stT209 40 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 39
    simpa using h
  have hprev := st209_p39
  have hstep := st209_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p41 : ((8936640895821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT209 (i+1))
      = (∑ i ∈ Finset.range 40, stT209 (i+1)) + stT209 41 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 40
    simpa using h
  have hprev := st209_p40
  have hstep := st209_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p42 : ((9011286660229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT209 (i+1))
      = (∑ i ∈ Finset.range 41, stT209 (i+1)) + stT209 42 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 41
    simpa using h
  have hprev := st209_p41
  have hstep := st209_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p43 : ((4884627264867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT209 (i+1))
      = (∑ i ∈ Finset.range 42, stT209 (i+1)) + stT209 43 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 42
    simpa using h
  have hprev := st209_p42
  have hstep := st209_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p44 : ((619979385991/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT209 (i+1))
      = (∑ i ∈ Finset.range 43, stT209 (i+1)) + stT209 44 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 43
    simpa using h
  have hprev := st209_p43
  have hstep := st209_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p45 : ((2296761773101/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT209 (i+1))
      = (∑ i ∈ Finset.range 44, stT209 (i+1)) + stT209 45 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 44
    simpa using h
  have hprev := st209_p44
  have hstep := st209_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p46 : ((4568982931117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT209 (i+1))
      = (∑ i ∈ Finset.range 45, stT209 (i+1)) + stT209 46 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 45
    simpa using h
  have hprev := st209_p45
  have hstep := st209_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p47 : ((1232369455231/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT209 (i+1))
      = (∑ i ∈ Finset.range 46, stT209 (i+1)) + stT209 47 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 46
    simpa using h
  have hprev := st209_p46
  have hstep := st209_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p48 : ((74503469531/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT209 (i+1))
      = (∑ i ∈ Finset.range 47, stT209 (i+1)) + stT209 48 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 47
    simpa using h
  have hprev := st209_p47
  have hstep := st209_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p49 : ((141777293313/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT209 (i+1))
      = (∑ i ∈ Finset.range 48, stT209 (i+1)) + stT209 49 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 48
    simpa using h
  have hprev := st209_p48
  have hstep := st209_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p50 : ((19529198029833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT209 (i+1))
      = (∑ i ∈ Finset.range 49, stT209 (i+1)) + stT209 50 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 49
    simpa using h
  have hprev := st209_p49
  have hstep := st209_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p51 : ((9518542337737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT209 (i+1))
      = (∑ i ∈ Finset.range 50, stT209 (i+1)) + stT209 51 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 50
    simpa using h
  have hprev := st209_p50
  have hstep := st209_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p52 : ((18303053796407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT209 (i+1))
      = (∑ i ∈ Finset.range 51, stT209 (i+1)) + stT209 52 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 51
    simpa using h
  have hprev := st209_p51
  have hstep := st209_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p53 : ((9827974476911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT209 (i+1))
      = (∑ i ∈ Finset.range 52, stT209 (i+1)) + stT209 53 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 52
    simpa using h
  have hprev := st209_p52
  have hstep := st209_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p54 : ((9263116547359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT209 (i+1))
      = (∑ i ∈ Finset.range 53, stT209 (i+1)) + stT209 54 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 53
    simpa using h
  have hprev := st209_p53
  have hstep := st209_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p55 : ((18906507232299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT209 (i+1))
      = (∑ i ∈ Finset.range 54, stT209 (i+1)) + stT209 55 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 54
    simpa using h
  have hprev := st209_p54
  have hstep := st209_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p56 : ((3869993679247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT209 (i+1))
      = (∑ i ∈ Finset.range 55, stT209 (i+1)) + stT209 56 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 55
    simpa using h
  have hprev := st209_p55
  have hstep := st209_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p57 : ((18315704154119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT209 (i+1))
      = (∑ i ∈ Finset.range 56, stT209 (i+1)) + stT209 57 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 56
    simpa using h
  have hprev := st209_p56
  have hstep := st209_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p58 : ((3921424196203/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT209 (i+1))
      = (∑ i ∈ Finset.range 57, stT209 (i+1)) + stT209 58 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 57
    simpa using h
  have hprev := st209_p57
  have hstep := st209_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p59 : ((733820145851/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT209 (i+1))
      = (∑ i ∈ Finset.range 58, stT209 (i+1)) + stT209 59 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 58
    simpa using h
  have hprev := st209_p58
  have hstep := st209_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p60 : ((19395645932653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT209 (i+1))
      = (∑ i ∈ Finset.range 59, stT209 (i+1)) + stT209 60 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 59
    simpa using h
  have hprev := st209_p59
  have hstep := st209_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p61 : ((18633941610863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT209 (i+1))
      = (∑ i ∈ Finset.range 60, stT209 (i+1)) + stT209 61 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 60
    simpa using h
  have hprev := st209_p60
  have hstep := st209_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p62 : ((19105231361957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT209 (i+1))
      = (∑ i ∈ Finset.range 61, stT209 (i+1)) + stT209 62 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 61
    simpa using h
  have hprev := st209_p61
  have hstep := st209_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p63 : ((18882402332027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT209 (i+1))
      = (∑ i ∈ Finset.range 62, stT209 (i+1)) + stT209 63 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 62
    simpa using h
  have hprev := st209_p62
  have hstep := st209_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p64 : ((18917268582027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT209 (i+1))
      = (∑ i ∈ Finset.range 63, stT209 (i+1)) + stT209 64 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 63
    simpa using h
  have hprev := st209_p63
  have hstep := st209_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p65 : ((1900499708499/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT209 (i+1))
      = (∑ i ∈ Finset.range 64, stT209 (i+1)) + stT209 65 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 64
    simpa using h
  have hprev := st209_p64
  have hstep := st209_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p66 : ((29464676787/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT209 (i+1))
      = (∑ i ∈ Finset.range 65, stT209 (i+1)) + stT209 66 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 65
    simpa using h
  have hprev := st209_p65
  have hstep := st209_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p67 : ((9502690301491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT209 (i+1))
      = (∑ i ∈ Finset.range 66, stT209 (i+1)) + stT209 67 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 66
    simpa using h
  have hprev := st209_p66
  have hstep := st209_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p68 : ((18912948996923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT209 (i+1))
      = (∑ i ∈ Finset.range 67, stT209 (i+1)) + stT209 68 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 67
    simpa using h
  have hprev := st209_p67
  have hstep := st209_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p69 : ((18895796413891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT209 (i+1))
      = (∑ i ∈ Finset.range 68, stT209 (i+1)) + stT209 69 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 68
    simpa using h
  have hprev := st209_p68
  have hstep := st209_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p70 : ((3814527991663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT209 (i+1))
      = (∑ i ∈ Finset.range 69, stT209 (i+1)) + stT209 70 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 69
    simpa using h
  have hprev := st209_p69
  have hstep := st209_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p71 : ((18692995517207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT209 (i+1))
      = (∑ i ∈ Finset.range 70, stT209 (i+1)) + stT209 71 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 70
    simpa using h
  have hprev := st209_p70
  have hstep := st209_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p72 : ((19302910315037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT209 (i+1))
      = (∑ i ∈ Finset.range 71, stT209 (i+1)) + stT209 72 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 71
    simpa using h
  have hprev := st209_p71
  have hstep := st209_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p73 : ((18460958057069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT209 (i+1))
      = (∑ i ∈ Finset.range 72, stT209 (i+1)) + stT209 73 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 72
    simpa using h
  have hprev := st209_p72
  have hstep := st209_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p74 : ((3899469452041/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT209 (i+1))
      = (∑ i ∈ Finset.range 73, stT209 (i+1)) + stT209 74 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 73
    simpa using h
  have hprev := st209_p73
  have hstep := st209_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p75 : ((2294113510999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT209 (i+1))
      = (∑ i ∈ Finset.range 74, stT209 (i+1)) + stT209 75 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 74
    simpa using h
  have hprev := st209_p74
  have hstep := st209_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p76 : ((9733586960901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT209 (i+1))
      = (∑ i ∈ Finset.range 75, stT209 (i+1)) + stT209 76 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 75
    simpa using h
  have hprev := st209_p75
  have hstep := st209_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p77 : ((9279628329619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT209 (i+1))
      = (∑ i ∈ Finset.range 76, stT209 (i+1)) + stT209 77 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 76
    simpa using h
  have hprev := st209_p76
  have hstep := st209_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p78 : ((19078986521839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT209 (i+1))
      = (∑ i ∈ Finset.range 77, stT209 (i+1)) + stT209 78 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 77
    simpa using h
  have hprev := st209_p77
  have hstep := st209_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p79 : ((2385175822997/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT209 (i+1))
      = (∑ i ∈ Finset.range 78, stT209 (i+1)) + stT209 79 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 78
    simpa using h
  have hprev := st209_p78
  have hstep := st209_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p80 : ((2316356358161/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT209 (i+1))
      = (∑ i ∈ Finset.range 79, stT209 (i+1)) + stT209 80 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 79
    simpa using h
  have hprev := st209_p79
  have hstep := st209_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p81 : ((1950014187947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT209 (i+1))
      = (∑ i ∈ Finset.range 80, stT209 (i+1)) + stT209 81 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 80
    simpa using h
  have hprev := st209_p80
  have hstep := st209_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p82 : ((9199104496699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT209 (i+1))
      = (∑ i ∈ Finset.range 81, stT209 (i+1)) + stT209 82 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 81
    simpa using h
  have hprev := st209_p81
  have hstep := st209_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p83 : ((1203456902037/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT209 (i+1))
      = (∑ i ∈ Finset.range 82, stT209 (i+1)) + stT209 83 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 82
    simpa using h
  have hprev := st209_p82
  have hstep := st209_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p84 : ((9488677082001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT209 (i+1))
      = (∑ i ∈ Finset.range 83, stT209 (i+1)) + stT209 84 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 83
    simpa using h
  have hprev := st209_p83
  have hstep := st209_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p85 : ((29670874707/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT209 (i+1))
      = (∑ i ∈ Finset.range 84, stT209 (i+1)) + stT209 85 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 84
    simpa using h
  have hprev := st209_p84
  have hstep := st209_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p86 : ((9754516902011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT209 (i+1))
      = (∑ i ∈ Finset.range 85, stT209 (i+1)) + stT209 86 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 85
    simpa using h
  have hprev := st209_p85
  have hstep := st209_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p87 : ((18473551688893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT209 (i+1))
      = (∑ i ∈ Finset.range 86, stT209 (i+1)) + stT209 87 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 86
    simpa using h
  have hprev := st209_p86
  have hstep := st209_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p88 : ((4758907638181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT209 (i+1))
      = (∑ i ∈ Finset.range 87, stT209 (i+1)) + stT209 88 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 87
    simpa using h
  have hprev := st209_p87
  have hstep := st209_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p89 : ((9635800362441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT209 (i+1))
      = (∑ i ∈ Finset.range 88, stT209 (i+1)) + stT209 89 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 88
    simpa using h
  have hprev := st209_p88
  have hstep := st209_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p90 : ((4591844139859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT209 (i+1))
      = (∑ i ∈ Finset.range 89, stT209 (i+1)) + stT209 90 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 89
    simpa using h
  have hprev := st209_p89
  have hstep := st209_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p91 : ((1210696573711/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT209 (i+1))
      = (∑ i ∈ Finset.range 90, stT209 (i+1)) + stT209 91 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 90
    simpa using h
  have hprev := st209_p90
  have hstep := st209_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p92 : ((18944946549841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT209 (i+1))
      = (∑ i ∈ Finset.range 91, stT209 (i+1)) + stT209 92 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 91
    simpa using h
  have hprev := st209_p91
  have hstep := st209_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p93 : ((18483579644289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT209 (i+1))
      = (∑ i ∈ Finset.range 92, stT209 (i+1)) + stT209 93 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 92
    simpa using h
  have hprev := st209_p92
  have hstep := st209_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p94 : ((19493668795167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT209 (i+1))
      = (∑ i ∈ Finset.range 93, stT209 (i+1)) + stT209 94 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 93
    simpa using h
  have hprev := st209_p93
  have hstep := st209_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p95 : ((3745331841303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT209 (i+1))
      = (∑ i ∈ Finset.range 94, stT209 (i+1)) + stT209 95 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 94
    simpa using h
  have hprev := st209_p94
  have hstep := st209_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p96 : ((4653960299739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT209 (i+1))
      = (∑ i ∈ Finset.range 95, stT209 (i+1)) + stT209 96 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 95
    simpa using h
  have hprev := st209_p95
  have hstep := st209_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p97 : ((9756716223303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT209 (i+1))
      = (∑ i ∈ Finset.range 96, stT209 (i+1)) + stT209 97 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 96
    simpa using h
  have hprev := st209_p96
  have hstep := st209_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p98 : ((9316307698057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT209 (i+1))
      = (∑ i ∈ Finset.range 97, stT209 (i+1)) + stT209 98 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 97
    simpa using h
  have hprev := st209_p97
  have hstep := st209_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p99 : ((18672110335103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT209 (i+1))
      = (∑ i ∈ Finset.range 98, stT209 (i+1)) + stT209 99 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 98
    simpa using h
  have hprev := st209_p98
  have hstep := st209_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p100 : ((1219653780797/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT209 (i+1))
      = (∑ i ∈ Finset.range 99, stT209 (i+1)) + stT209 100 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 99
    simpa using h
  have hprev := st209_p99
  have hstep := st209_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p101 : ((9318905559477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT209 (i+1))
      = (∑ i ∈ Finset.range 100, stT209 (i+1)) + stT209 101 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 100
    simpa using h
  have hprev := st209_p100
  have hstep := st209_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p102 : ((9316627724003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT209 (i+1))
      = (∑ i ∈ Finset.range 101, stT209 (i+1)) + stT209 102 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 101
    simpa using h
  have hprev := st209_p101
  have hstep := st209_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p103 : ((9757249116881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT209 (i+1))
      = (∑ i ∈ Finset.range 102, stT209 (i+1)) + stT209 103 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 102
    simpa using h
  have hprev := st209_p102
  have hstep := st209_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p104 : ((18738943973309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT209 (i+1))
      = (∑ i ∈ Finset.range 103, stT209 (i+1)) + stT209 104 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 103
    simpa using h
  have hprev := st209_p103
  have hstep := st209_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p105 : ((3703405988263/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT209 (i+1))
      = (∑ i ∈ Finset.range 104, stT209 (i+1)) + stT209 105 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 104
    simpa using h
  have hprev := st209_p104
  have hstep := st209_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p106 : ((3894483389687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT209 (i+1))
      = (∑ i ∈ Finset.range 105, stT209 (i+1)) + stT209 106 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 105
    simpa using h
  have hprev := st209_p105
  have hstep := st209_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p107 : ((18948592438459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT209 (i+1))
      = (∑ i ∈ Finset.range 106, stT209 (i+1)) + stT209 107 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 106
    simpa using h
  have hprev := st209_p106
  have hstep := st209_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p108 : ((18385677527961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT209 (i+1))
      = (∑ i ∈ Finset.range 107, stT209 (i+1)) + stT209 108 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 107
    simpa using h
  have hprev := st209_p107
  have hstep := st209_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p109 : ((19308922178057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT209 (i+1))
      = (∑ i ∈ Finset.range 108, stT209 (i+1)) + stT209 109 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 108
    simpa using h
  have hprev := st209_p108
  have hstep := st209_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p110 : ((1924356324287/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT209 (i+1))
      = (∑ i ∈ Finset.range 109, stT209 (i+1)) + stT209 110 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 109
    simpa using h
  have hprev := st209_p109
  have hstep := st209_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p111 : ((9182668859263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT209 (i+1))
      = (∑ i ∈ Finset.range 110, stT209 (i+1)) + stT209 111 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 110
    simpa using h
  have hprev := st209_p110
  have hstep := st209_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p112 : ((18968819302341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT209 (i+1))
      = (∑ i ∈ Finset.range 111, stT209 (i+1)) + stT209 112 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 111
    simpa using h
  have hprev := st209_p111
  have hstep := st209_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p113 : ((19492905702981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT209 (i+1))
      = (∑ i ∈ Finset.range 112, stT209 (i+1)) + stT209 113 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 112
    simpa using h
  have hprev := st209_p112
  have hstep := st209_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p114 : ((18603919813259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT209 (i+1))
      = (∑ i ∈ Finset.range 113, stT209 (i+1)) + stT209 114 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 113
    simpa using h
  have hprev := st209_p113
  have hstep := st209_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p115 : ((9271280025877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT209 (i+1))
      = (∑ i ∈ Finset.range 114, stT209 (i+1)) + stT209 115 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 114
    simpa using h
  have hprev := st209_p114
  have hstep := st209_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p116 : ((9728570704207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT209 (i+1))
      = (∑ i ∈ Finset.range 115, stT209 (i+1)) + stT209 116 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 115
    simpa using h
  have hprev := st209_p115
  have hstep := st209_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p117 : ((19100362604999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT209 (i+1))
      = (∑ i ∈ Finset.range 116, stT209 (i+1)) + stT209 117 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 116
    simpa using h
  have hprev := st209_p116
  have hstep := st209_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p118 : ((18342663098599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT209 (i+1))
      = (∑ i ∈ Finset.range 117, stT209 (i+1)) + stT209 118 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 117
    simpa using h
  have hprev := st209_p117
  have hstep := st209_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p119 : ((18998295591877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT209 (i+1))
      = (∑ i ∈ Finset.range 118, stT209 (i+1)) + stT209 119 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 118
    simpa using h
  have hprev := st209_p118
  have hstep := st209_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p120 : ((19510390101517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT209 (i+1))
      = (∑ i ∈ Finset.range 119, stT209 (i+1)) + stT209 120 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 119
    simpa using h
  have hprev := st209_p119
  have hstep := st209_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p121 : ((18684759109863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT209 (i+1))
      = (∑ i ∈ Finset.range 120, stT209 (i+1)) + stT209 121 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 120
    simpa using h
  have hprev := st209_p120
  have hstep := st209_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p122 : ((18432261101169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT209 (i+1))
      = (∑ i ∈ Finset.range 121, stT209 (i+1)) + stT209 122 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 121
    simpa using h
  have hprev := st209_p121
  have hstep := st209_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p123 : ((4831031563533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT209 (i+1))
      = (∑ i ∈ Finset.range 122, stT209 (i+1)) + stT209 123 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 122
    simpa using h
  have hprev := st209_p122
  have hstep := st209_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p124 : ((9673596025971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT209 (i+1))
      = (∑ i ∈ Finset.range 123, stT209 (i+1)) + stT209 124 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 123
    simpa using h
  have hprev := st209_p123
  have hstep := st209_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p125 : ((1845573891947/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT209 (i+1))
      = (∑ i ∈ Finset.range 124, stT209 (i+1)) + stT209 125 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 124
    simpa using h
  have hprev := st209_p124
  have hstep := st209_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p126 : ((930617025121/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT209 (i+1))
      = (∑ i ∈ Finset.range 125, stT209 (i+1)) + stT209 126 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 125
    simpa using h
  have hprev := st209_p125
  have hstep := st209_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p127 : ((304222733089/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT209 (i+1))
      = (∑ i ∈ Finset.range 126, stT209 (i+1)) + stT209 127 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 126
    simpa using h
  have hprev := st209_p126
  have hstep := st209_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p128 : ((299791822597/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT209 (i+1))
      = (∑ i ∈ Finset.range 127, stT209 (i+1)) + stT209 128 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 127
    simpa using h
  have hprev := st209_p127
  have hstep := st209_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p129 : ((9184861005713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT209 (i+1))
      = (∑ i ∈ Finset.range 128, stT209 (i+1)) + stT209 129 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 128
    simpa using h
  have hprev := st209_p128
  have hstep := st209_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p130 : ((4682894869531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT209 (i+1))
      = (∑ i ∈ Finset.range 129, stT209 (i+1)) + stT209 130 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 129
    simpa using h
  have hprev := st209_p129
  have hstep := st209_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p131 : ((4878982660937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT209 (i+1))
      = (∑ i ∈ Finset.range 130, stT209 (i+1)) + stT209 131 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 130
    simpa using h
  have hprev := st209_p130
  have hstep := st209_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p132 : ((382361829977/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT209 (i+1))
      = (∑ i ∈ Finset.range 131, stT209 (i+1)) + stT209 132 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 131
    simpa using h
  have hprev := st209_p131
  have hstep := st209_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p133 : ((458735417329/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT209 (i+1))
      = (∑ i ∈ Finset.range 132, stT209 (i+1)) + stT209 133 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 132
    simpa using h
  have hprev := st209_p132
  have hstep := st209_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p134 : ((9152930309/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT209 (i+1))
      = (∑ i ∈ Finset.range 133, stT209 (i+1)) + stT209 134 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 133
    simpa using h
  have hprev := st209_p133
  have hstep := st209_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p135 : ((4879176824063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT209 (i+1))
      = (∑ i ∈ Finset.range 134, stT209 (i+1)) + stT209 135 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 134
    simpa using h
  have hprev := st209_p134
  have hstep := st209_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p136 : ((19158634511819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT209 (i+1))
      = (∑ i ∈ Finset.range 135, stT209 (i+1)) + stT209 136 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 135
    simpa using h
  have hprev := st209_p135
  have hstep := st209_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p137 : ((18368741240351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT209 (i+1))
      = (∑ i ∈ Finset.range 136, stT209 (i+1)) + stT209 137 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 136
    simpa using h
  have hprev := st209_p136
  have hstep := st209_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p138 : ((746112350903/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT209 (i+1))
      = (∑ i ∈ Finset.range 137, stT209 (i+1)) + stT209 138 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 137
    simpa using h
  have hprev := st209_p137
  have hstep := st209_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p139 : ((19468266045843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT209 (i+1))
      = (∑ i ∈ Finset.range 138, stT209 (i+1)) + stT209 139 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 138
    simpa using h
  have hprev := st209_p138
  have hstep := st209_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p140 : ((19295392971213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT209 (i+1))
      = (∑ i ∈ Finset.range 139, stT209 (i+1)) + stT209 140 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 139
    simpa using h
  have hprev := st209_p139
  have hstep := st209_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p141 : ((18459529320197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT209 (i+1))
      = (∑ i ∈ Finset.range 140, stT209 (i+1)) + stT209 141 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 140
    simpa using h
  have hprev := st209_p140
  have hstep := st209_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p142 : ((18483768224201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT209 (i+1))
      = (∑ i ∈ Finset.range 141, stT209 (i+1)) + stT209 142 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 141
    simpa using h
  have hprev := st209_p141
  have hstep := st209_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p143 : ((19317606028451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT209 (i+1))
      = (∑ i ∈ Finset.range 142, stT209 (i+1)) + stT209 143 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 142
    simpa using h
  have hprev := st209_p142
  have hstep := st209_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p144 : ((19474569298999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT209 (i+1))
      = (∑ i ∈ Finset.range 143, stT209 (i+1)) + stT209 144 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 143
    simpa using h
  have hprev := st209_p143
  have hstep := st209_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p145 : ((9342332293097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT209 (i+1))
      = (∑ i ∈ Finset.range 144, stT209 (i+1)) + stT209 145 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 144
    simpa using h
  have hprev := st209_p144
  have hstep := st209_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p146 : ((1832590235083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT209 (i+1))
      = (∑ i ∈ Finset.range 145, stT209 (i+1)) + stT209 146 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 145
    simpa using h
  have hprev := st209_p145
  have hstep := st209_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p147 : ((2376257895327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT209 (i+1))
      = (∑ i ∈ Finset.range 146, stT209 (i+1)) + stT209 147 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 146
    simpa using h
  have hprev := st209_p146
  have hstep := st209_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p148 : ((1956811571121/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT209 (i+1))
      = (∑ i ∈ Finset.range 147, stT209 (i+1)) + stT209 148 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 147
    simpa using h
  have hprev := st209_p147
  have hstep := st209_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p149 : ((15252066149/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT209 (i+1))
      = (∑ i ∈ Finset.range 148, stT209 (i+1)) + stT209 149 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 148
    simpa using h
  have hprev := st209_p148
  have hstep := st209_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p150 : ((9171979533913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT209 (i+1))
      = (∑ i ∈ Finset.range 149, stT209 (i+1)) + stT209 150 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 149
    simpa using h
  have hprev := st209_p149
  have hstep := st209_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p151 : ((9294613316573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT209 (i+1))
      = (∑ i ∈ Finset.range 150, stT209 (i+1)) + stT209 151 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 150
    simpa using h
  have hprev := st209_p150
  have hstep := st209_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p152 : ((4848734942899/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT209 (i+1))
      = (∑ i ∈ Finset.range 151, stT209 (i+1)) + stT209 152 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 151
    simpa using h
  have hprev := st209_p151
  have hstep := st209_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p153 : ((4865953757821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT209 (i+1))
      = (∑ i ∈ Finset.range 152, stT209 (i+1)) + stT209 153 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 152
    simpa using h
  have hprev := st209_p152
  have hstep := st209_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p154 : ((18692660954213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT209 (i+1))
      = (∑ i ∈ Finset.range 153, stT209 (i+1)) + stT209 154 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 153
    simpa using h
  have hprev := st209_p153
  have hstep := st209_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p155 : ((18298675118453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT209 (i+1))
      = (∑ i ∈ Finset.range 154, stT209 (i+1)) + stT209 155 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 154
    simpa using h
  have hprev := st209_p154
  have hstep := st209_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p156 : ((18890231985653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT209 (i+1))
      = (∑ i ∈ Finset.range 155, stT209 (i+1)) + stT209 156 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 155
    simpa using h
  have hprev := st209_p155
  have hstep := st209_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p157 : ((19550626602331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT209 (i+1))
      = (∑ i ∈ Finset.range 156, stT209 (i+1)) + stT209 157 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 156
    simpa using h
  have hprev := st209_p156
  have hstep := st209_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p158 : ((19276072376509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT209 (i+1))
      = (∑ i ∈ Finset.range 157, stT209 (i+1)) + stT209 158 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 157
    simpa using h
  have hprev := st209_p157
  have hstep := st209_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p159 : ((18486953121377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT209 (i+1))
      = (∑ i ∈ Finset.range 158, stT209 (i+1)) + stT209 159 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 158
    simpa using h
  have hprev := st209_p158
  have hstep := st209_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p160 : ((18360710160357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT209 (i+1))
      = (∑ i ∈ Finset.range 159, stT209 (i+1)) + stT209 160 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 159
    simpa using h
  have hprev := st209_p159
  have hstep := st209_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p161 : ((19077382717517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT209 (i+1))
      = (∑ i ∈ Finset.range 160, stT209 (i+1)) + stT209 161 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 160
    simpa using h
  have hprev := st209_p160
  have hstep := st209_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p162 : ((19586853022817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT209 (i+1))
      = (∑ i ∈ Finset.range 161, stT209 (i+1)) + stT209 162 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 161
    simpa using h
  have hprev := st209_p161
  have hstep := st209_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p163 : ((19157206166921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT209 (i+1))
      = (∑ i ∈ Finset.range 162, stT209 (i+1)) + stT209 163 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 162
    simpa using h
  have hprev := st209_p162
  have hstep := st209_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p164 : ((18408468364533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT209 (i+1))
      = (∑ i ∈ Finset.range 163, stT209 (i+1)) + stT209 164 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 163
    simpa using h
  have hprev := st209_p163
  have hstep := st209_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p165 : ((9199449138163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT209 (i+1))
      = (∑ i ∈ Finset.range 164, stT209 (i+1)) + stT209 165 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 164
    simpa using h
  have hprev := st209_p164
  have hstep := st209_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p166 : ((2391945011597/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT209 (i+1))
      = (∑ i ∈ Finset.range 165, stT209 (i+1)) + stT209 166 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 165
    simpa using h
  have hprev := st209_p165
  have hstep := st209_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p167 : ((19594984224637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT209 (i+1))
      = (∑ i ∈ Finset.range 166, stT209 (i+1)) + stT209 167 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 166
    simpa using h
  have hprev := st209_p166
  have hstep := st209_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p168 : ((957584260763/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT209 (i+1))
      = (∑ i ∈ Finset.range 167, stT209 (i+1)) + stT209 168 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 167
    simpa using h
  have hprev := st209_p167
  have hstep := st209_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p169 : ((46031789407/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT209 (i+1))
      = (∑ i ∈ Finset.range 168, stT209 (i+1)) + stT209 169 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 168
    simpa using h
  have hprev := st209_p168
  have hstep := st209_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p170 : ((918481690241/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT209 (i+1))
      = (∑ i ∈ Finset.range 169, stT209 (i+1)) + stT209 170 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 169
    simpa using h
  have hprev := st209_p169
  have hstep := st209_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p171 : ((9536804057887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT209 (i+1))
      = (∑ i ∈ Finset.range 170, stT209 (i+1)) + stT209 171 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 170
    simpa using h
  have hprev := st209_p170
  have hstep := st209_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p172 : ((9797570603197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT209 (i+1))
      = (∑ i ∈ Finset.range 171, stT209 (i+1)) + stT209 172 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 171
    simpa using h
  have hprev := st209_p171
  have hstep := st209_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p173 : ((2407340566889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT209 (i+1))
      = (∑ i ∈ Finset.range 172, stT209 (i+1)) + stT209 173 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 172
    simpa using h
  have hprev := st209_p172
  have hstep := st209_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p174 : ((18503802728021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT209 (i+1))
      = (∑ i ∈ Finset.range 173, stT209 (i+1)) + stT209 174 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 173
    simpa using h
  have hprev := st209_p173
  have hstep := st209_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p175 : ((2286771345691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT209 (i+1))
      = (∑ i ∈ Finset.range 174, stT209 (i+1)) + stT209 175 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 174
    simpa using h
  have hprev := st209_p174
  have hstep := st209_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p176 : ((9444606458921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT209 (i+1))
      = (∑ i ∈ Finset.range 175, stT209 (i+1)) + stT209 176 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 175
    simpa using h
  have hprev := st209_p175
  have hstep := st209_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p177 : ((9770118033911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT209 (i+1))
      = (∑ i ∈ Finset.range 176, stT209 (i+1)) + stT209 177 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 176
    simpa using h
  have hprev := st209_p176
  have hstep := st209_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p178 : ((1944306598981/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT209 (i+1))
      = (∑ i ∈ Finset.range 177, stT209 (i+1)) + stT209 178 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 177
    simpa using h
  have hprev := st209_p177
  have hstep := st209_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p179 : ((9361331627529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT209 (i+1))
      = (∑ i ∈ Finset.range 178, stT209 (i+1)) + stT209 179 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 178
    simpa using h
  have hprev := st209_p178
  have hstep := st209_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p180 : ((9128015820273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT209 (i+1))
      = (∑ i ∈ Finset.range 179, stT209 (i+1)) + stT209 180 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 179
    simpa using h
  have hprev := st209_p179
  have hstep := st209_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p181 : ((1860021095407/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT209 (i+1))
      = (∑ i ∈ Finset.range 180, stT209 (i+1)) + stT209 181 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 180
    simpa using h
  have hprev := st209_p180
  have hstep := st209_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p182 : ((9669994658027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT209 (i+1))
      = (∑ i ∈ Finset.range 181, stT209 (i+1)) + stT209 182 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 181
    simpa using h
  have hprev := st209_p181
  have hstep := st209_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p183 : ((4900675266811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT209 (i+1))
      = (∑ i ∈ Finset.range 182, stT209 (i+1)) + stT209 183 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 182
    simpa using h
  have hprev := st209_p182
  have hstep := st209_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p184 : ((9543260316117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT209 (i+1))
      = (∑ i ∈ Finset.range 183, stT209 (i+1)) + stT209 184 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 183
    simpa using h
  have hprev := st209_p183
  have hstep := st209_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p185 : ((18392766611729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT209 (i+1))
      = (∑ i ∈ Finset.range 184, stT209 (i+1)) + stT209 185 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 184
    simpa using h
  have hprev := st209_p184
  have hstep := st209_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p186 : ((18314763499577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT209 (i+1))
      = (∑ i ∈ Finset.range 185, stT209 (i+1)) + stT209 186 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 185
    simpa using h
  have hprev := st209_p185
  have hstep := st209_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p187 : ((18935590026873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT209 (i+1))
      = (∑ i ∈ Finset.range 186, stT209 (i+1)) + stT209 187 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 186
    simpa using h
  have hprev := st209_p186
  have hstep := st209_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p188 : ((19554255155001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT209 (i+1))
      = (∑ i ∈ Finset.range 187, stT209 (i+1)) + stT209 188 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 187
    simpa using h
  have hprev := st209_p187
  have hstep := st209_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p189 : ((19484527262021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT209 (i+1))
      = (∑ i ∈ Finset.range 188, stT209 (i+1)) + stT209 189 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 188
    simpa using h
  have hprev := st209_p188
  have hstep := st209_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p190 : ((18808620654477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT209 (i+1))
      = (∑ i ∈ Finset.range 189, stT209 (i+1)) + stT209 190 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 189
    simpa using h
  have hprev := st209_p189
  have hstep := st209_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p191 : ((4566768673413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT209 (i+1))
      = (∑ i ∈ Finset.range 190, stT209 (i+1)) + stT209 191 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 190
    simpa using h
  have hprev := st209_p190
  have hstep := st209_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p192 : ((18442620004593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT209 (i+1))
      = (∑ i ∈ Finset.range 191, stT209 (i+1)) + stT209 192 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 191
    simpa using h
  have hprev := st209_p191
  have hstep := st209_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p193 : ((299091930727/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT209 (i+1))
      = (∑ i ∈ Finset.range 192, stT209 (i+1)) + stT209 193 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 192
    simpa using h
  have hprev := st209_p192
  have hstep := st209_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p194 : ((4905159156959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT209 (i+1))
      = (∑ i ∈ Finset.range 193, stT209 (i+1)) + stT209 194 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 193
    simpa using h
  have hprev := st209_p193
  have hstep := st209_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p195 : ((9689360045383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT209 (i+1))
      = (∑ i ∈ Finset.range 194, stT209 (i+1)) + stT209 195 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 194
    simpa using h
  have hprev := st209_p194
  have hstep := st209_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p196 : ((9336602761423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT209 (i+1))
      = (∑ i ∈ Finset.range 195, stT209 (i+1)) + stT209 196 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 195
    simpa using h
  have hprev := st209_p195
  have hstep := st209_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p197 : ((18233886642123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT209 (i+1))
      = (∑ i ∈ Finset.range 196, stT209 (i+1)) + stT209 197 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 196
    simpa using h
  have hprev := st209_p196
  have hstep := st209_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p198 : ((1156660868173/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT209 (i+1))
      = (∑ i ∈ Finset.range 197, stT209 (i+1)) + stT209 198 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 197
    simpa using h
  have hprev := st209_p197
  have hstep := st209_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p199 : ((3841994622799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT209 (i+1))
      = (∑ i ∈ Finset.range 198, stT209 (i+1)) + stT209 199 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 198
    simpa using h
  have hprev := st209_p198
  have hstep := st209_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p200 : ((19636302170621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT209 (i+1))
      = (∑ i ∈ Finset.range 199, stT209 (i+1)) + stT209 200 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 199
    simpa using h
  have hprev := st209_p199
  have hstep := st209_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p201 : ((19364721389549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT209 (i+1))
      = (∑ i ∈ Finset.range 200, stT209 (i+1)) + stT209 201 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 200
    simpa using h
  have hprev := st209_p200
  have hstep := st209_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p202 : ((18667816717323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT209 (i+1))
      = (∑ i ∈ Finset.range 201, stT209 (i+1)) + stT209 202 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 201
    simpa using h
  have hprev := st209_p201
  have hstep := st209_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p203 : ((18228041995057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT209 (i+1))
      = (∑ i ∈ Finset.range 202, stT209 (i+1)) + stT209 203 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 202
    simpa using h
  have hprev := st209_p202
  have hstep := st209_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p204 : ((18468037384537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT209 (i+1))
      = (∑ i ∈ Finset.range 203, stT209 (i+1)) + stT209 204 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 203
    simpa using h
  have hprev := st209_p203
  have hstep := st209_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p205 : ((19152668503027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT209 (i+1))
      = (∑ i ∈ Finset.range 204, stT209 (i+1)) + stT209 205 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 204
    simpa using h
  have hprev := st209_p204
  have hstep := st209_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p206 : ((981444310263/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT209 (i+1))
      = (∑ i ∈ Finset.range 205, stT209 (i+1)) + stT209 206 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 205
    simpa using h
  have hprev := st209_p205
  have hstep := st209_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p207 : ((3890102461029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT209 (i+1))
      = (∑ i ∈ Finset.range 206, stT209 (i+1)) + stT209 207 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 206
    simpa using h
  have hprev := st209_p206
  have hstep := st209_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p208 : ((18788910953721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT209 (i+1))
      = (∑ i ∈ Finset.range 207, stT209 (i+1)) + stT209 208 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 207
    simpa using h
  have hprev := st209_p207
  have hstep := st209_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p209 : ((4564770022579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT209 (i+1))
      = (∑ i ∈ Finset.range 208, stT209 (i+1)) + stT209 209 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 208
    simpa using h
  have hprev := st209_p208
  have hstep := st209_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p210 : ((18345184330821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT209 (i+1))
      = (∑ i ∈ Finset.range 209, stT209 (i+1)) + stT209 210 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 209
    simpa using h
  have hprev := st209_p209
  have hstep := st209_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p211 : ((18964211904141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT209 (i+1))
      = (∑ i ∈ Finset.range 210, stT209 (i+1)) + stT209 211 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 210
    simpa using h
  have hprev := st209_p210
  have hstep := st209_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p212 : ((3910973973153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT209 (i+1))
      = (∑ i ∈ Finset.range 211, stT209 (i+1)) + stT209 212 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 211
    simpa using h
  have hprev := st209_p211
  have hstep := st209_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p213 : ((19590351641157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT209 (i+1))
      = (∑ i ∈ Finset.range 212, stT209 (i+1)) + stT209 213 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 212
    simpa using h
  have hprev := st209_p212
  have hstep := st209_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p214 : ((19043538211623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT209 (i+1))
      = (∑ i ∈ Finset.range 213, stT209 (i+1)) + stT209 214 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 213
    simpa using h
  have hprev := st209_p213
  have hstep := st209_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p215 : ((2299806171381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT209 (i+1))
      = (∑ i ∈ Finset.range 214, stT209 (i+1)) + stT209 215 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 214
    simpa using h
  have hprev := st209_p214
  have hstep := st209_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p216 : ((284636276223/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT209 (i+1))
      = (∑ i ∈ Finset.range 215, stT209 (i+1)) + stT209 216 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 215
    simpa using h
  have hprev := st209_p215
  have hstep := st209_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p217 : ((4662857064661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT209 (i+1))
      = (∑ i ∈ Finset.range 216, stT209 (i+1)) + stT209 217 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 216
    simpa using h
  have hprev := st209_p216
  have hstep := st209_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p218 : ((9663112456777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT209 (i+1))
      = (∑ i ∈ Finset.range 217, stT209 (i+1)) + stT209 218 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 217
    simpa using h
  have hprev := st209_p217
  have hstep := st209_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p219 : ((9833638743149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT209 (i+1))
      = (∑ i ∈ Finset.range 218, stT209 (i+1)) + stT209 219 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 218
    simpa using h
  have hprev := st209_p218
  have hstep := st209_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p220 : ((9695225820249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT209 (i+1))
      = (∑ i ∈ Finset.range 219, stT209 (i+1)) + stT209 220 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 219
    simpa using h
  have hprev := st209_p219
  have hstep := st209_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p221 : ((9365568963139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT209 (i+1))
      = (∑ i ∈ Finset.range 220, stT209 (i+1)) + stT209 221 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 220
    simpa using h
  have hprev := st209_p220
  have hstep := st209_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p222 : ((18237138856841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT209 (i+1))
      = (∑ i ∈ Finset.range 221, stT209 (i+1)) + stT209 222 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 221
    simpa using h
  have hprev := st209_p221
  have hstep := st209_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p223 : ((4578020656169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT209 (i+1))
      = (∑ i ∈ Finset.range 222, stT209 (i+1)) + stT209 223 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 222
    simpa using h
  have hprev := st209_p222
  have hstep := st209_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p224 : ((18890730516949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT209 (i+1))
      = (∑ i ∈ Finset.range 223, stT209 (i+1)) + stT209 224 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 223
    simpa using h
  have hprev := st209_p223
  have hstep := st209_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p225 : ((19502771904907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT209 (i+1))
      = (∑ i ∈ Finset.range 224, stT209 (i+1)) + stT209 225 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 224
    simpa using h
  have hprev := st209_p224
  have hstep := st209_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p226 : ((19658576032657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT209 (i+1))
      = (∑ i ∈ Finset.range 225, stT209 (i+1)) + stT209 226 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 225
    simpa using h
  have hprev := st209_p225
  have hstep := st209_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p227 : ((3847593764813/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT209 (i+1))
      = (∑ i ∈ Finset.range 226, stT209 (i+1)) + stT209 227 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 226
    simpa using h
  have hprev := st209_p226
  have hstep := st209_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p228 : ((2322006851547/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT209 (i+1))
      = (∑ i ∈ Finset.range 227, stT209 (i+1)) + stT209 228 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 227
    simpa using h
  have hprev := st209_p227
  have hstep := st209_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p229 : ((3638200570017/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT209 (i+1))
      = (∑ i ∈ Finset.range 228, stT209 (i+1)) + stT209 229 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 228
    simpa using h
  have hprev := st209_p228
  have hstep := st209_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p230 : ((3675740392177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT209 (i+1))
      = (∑ i ∈ Finset.range 229, stT209 (i+1)) + stT209 230 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 229
    simpa using h
  have hprev := st209_p229
  have hstep := st209_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p231 : ((9495404454529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT209 (i+1))
      = (∑ i ∈ Finset.range 230, stT209 (i+1)) + stT209 231 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 230
    simpa using h
  have hprev := st209_p230
  have hstep := st209_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p232 : ((9779044004893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT209 (i+1))
      = (∑ i ∈ Finset.range 231, stT209 (i+1)) + stT209 232 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 231
    simpa using h
  have hprev := st209_p231
  have hstep := st209_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p233 : ((19652350094871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT209 (i+1))
      = (∑ i ∈ Finset.range 232, stT209 (i+1)) + stT209 233 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 232
    simpa using h
  have hprev := st209_p232
  have hstep := st209_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p234 : ((19206406470069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT209 (i+1))
      = (∑ i ∈ Finset.range 233, stT209 (i+1)) + stT209 234 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 233
    simpa using h
  have hprev := st209_p233
  have hstep := st209_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p235 : ((9277846644501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT209 (i+1))
      = (∑ i ∈ Finset.range 234, stT209 (i+1)) + stT209 235 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 234
    simpa using h
  have hprev := st209_p234
  have hstep := st209_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p236 : ((18181577621987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT209 (i+1))
      = (∑ i ∈ Finset.range 235, stT209 (i+1)) + stT209 236 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 235
    simpa using h
  have hprev := st209_p235
  have hstep := st209_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p237 : ((2294468563333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT209 (i+1))
      = (∑ i ∈ Finset.range 236, stT209 (i+1)) + stT209 237 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 236
    simpa using h
  have hprev := st209_p236
  have hstep := st209_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p238 : ((9473884579921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT209 (i+1))
      = (∑ i ∈ Finset.range 237, stT209 (i+1)) + stT209 238 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 237
    simpa using h
  have hprev := st209_p237
  have hstep := st209_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p239 : ((1220512353713/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT209 (i+1))
      = (∑ i ∈ Finset.range 238, stT209 (i+1)) + stT209 239 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 238
    simpa using h
  have hprev := st209_p238
  have hstep := st209_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p240 : ((9841151161097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT209 (i+1))
      = (∑ i ∈ Finset.range 239, stT209 (i+1)) + stT209 240 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 239
    simpa using h
  have hprev := st209_p239
  have hstep := st209_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p241 : ((9651930042347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT209 (i+1))
      = (∑ i ∈ Finset.range 240, stT209 (i+1)) + stT209 241 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 240
    simpa using h
  have hprev := st209_p240
  have hstep := st209_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p242 : ((18662930775619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT209 (i+1))
      = (∑ i ∈ Finset.range 241, stT209 (i+1)) + stT209 242 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 241
    simpa using h
  have hprev := st209_p241
  have hstep := st209_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p243 : ((18208831462749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT209 (i+1))
      = (∑ i ∈ Finset.range 242, stT209 (i+1)) + stT209 243 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 242
    simpa using h
  have hprev := st209_p242
  have hstep := st209_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p244 : ((18254797954317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT209 (i+1))
      = (∑ i ∈ Finset.range 243, stT209 (i+1)) + stT209 244 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 243
    simpa using h
  have hprev := st209_p243
  have hstep := st209_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p245 : ((18765643203917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT209 (i+1))
      = (∑ i ∈ Finset.range 244, stT209 (i+1)) + stT209 245 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 244
    simpa using h
  have hprev := st209_p244
  have hstep := st209_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p246 : ((19389543836293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT209 (i+1))
      = (∑ i ∈ Finset.range 245, stT209 (i+1)) + stT209 246 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 245
    simpa using h
  have hprev := st209_p245
  have hstep := st209_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p247 : ((19703279569593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT209 (i+1))
      = (∑ i ∈ Finset.range 246, stT209 (i+1)) + stT209 247 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 246
    simpa using h
  have hprev := st209_p246
  have hstep := st209_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p248 : ((4874555467917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT209 (i+1))
      = (∑ i ∈ Finset.range 247, stT209 (i+1)) + stT209 248 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 247
    simpa using h
  have hprev := st209_p247
  have hstep := st209_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p249 : ((18914736688493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT209 (i+1))
      = (∑ i ∈ Finset.range 248, stT209 (i+1)) + stT209 249 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 248
    simpa using h
  have hprev := st209_p248
  have hstep := st209_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_p250 : ((733664126557/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT209 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT209 (i+1))
      = (∑ i ∈ Finset.range 249, stT209 (i+1)) + stT209 250 := by
    have h := Finset.sum_range_succ (fun i => stT209 (i+1)) 249
    simpa using h
  have hprev := st209_p249
  have hstep := st209_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st209_s250 :
    |Real.sin (((209 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((73017/125000 : ℚ) : ℝ))
      - ((-8459/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1352447/2000000) (δ := 131/12500000) (ψ := 73017/125000) 209 184
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 209`** (evaluated boundary). -/
theorem station_209_sign : hardyG ((((209:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 209 250 (by norm_num) (by norm_num)
    ((73017/125000 : ℚ) : ℝ)
  have hchain := st209_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT209 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((209 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((73017/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st209_c250
  have hsinb := abs_le.mp st209_s250
  have hbdy_lo : ((22474706224773/698900000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((209 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((73017/125000 : ℚ) : ℝ))) / 2
          - ((((209:ℕ)):ℝ))
            * Real.sin (((209 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((73017/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((209:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((209:ℝ) * Real.log (250:ℝ) - ((73017/125000 : ℚ) : ℝ))) / 2
        - ((209:ℝ)) * Real.sin ((209:ℝ) * Real.log (250:ℝ) - ((73017/125000 : ℚ) : ℝ))
        ≥ ((177678303/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((209:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((177678303/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((177678303/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((177678303/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((209:ℕ)):ℝ))+1) * (((((209:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((60710321067/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((733664126557/400000000000 : ℚ) : ℝ) + ((22474706224773/698900000000000 : ℚ) : ℝ)
      - ((60710321067/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((73017/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((209:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((73017/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((209:ℕ)):ℝ)))).re
      - Real.sin ((73017/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((209:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((209:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((209:ℕ)):ℝ))
      = (((((209:ℕ)):ℝ)) * (Real.log ((((209:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((209:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_209
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
  have hθwin : |(((73017/125000 : ℚ) : ℝ) + ((42:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((209:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((209:ℕ)):ℝ)))
    (φ := ((73017/125000 : ℚ) : ℝ) + ((42:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((73017/125000 : ℚ) : ℝ) + ((42:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((73017/125000 : ℚ)) : ℝ) - Real.pi) + ((42:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((73017/125000 : ℚ)) : ℝ) - Real.pi) 42).1,
    (cos_sin_shift ((((73017/125000 : ℚ)) : ℝ) - Real.pi) 42).2]
  exact cos_sin_flip ((73017/125000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_209_sign
end AxiomAudit
