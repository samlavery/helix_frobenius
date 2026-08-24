import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 242` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT242 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((242 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-1089/25000 : ℚ) : ℝ))

theorem st242_c1 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((999051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1089/100000) (δ := 1/1000000000) (ψ := -1089/25000) 242 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t1 : ((999001/1000000 : ℚ) : ℝ) ≤ stT242 1 := by
  have hc : ((999001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999001/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((999001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c2 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-285987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2326041/5000000) (δ := 2459/200000000) (ψ := -1089/25000) 242 27
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t2 : ((-505646769379/2500000000000 : ℚ) : ℝ) ≤ stT242 2 := by
  have hc : ((-286037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505646769379/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-286037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c3 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-428783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2517427/5000000) (δ := 12103/1000000000) (ψ := -1089/25000) 242 42
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t3 : ((-2475868611999/10000000000000 : ℚ) : ℝ) ≤ stT242 3 := by
  have hc : ((-428833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2475868611999/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-428833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c4 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-811769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6294929/10000000) (δ := 6141/500000000) (ψ := -1089/25000) 242 53
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t4 : ((-4059095811819/10000000000000 : ℚ) : ℝ) ≤ stT242 4 := by
  have hc : ((-811819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4059095811819/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-811819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c5 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((15618/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74863/10000000) (δ := 3039/250000000) (ψ := -1089/25000) 242 62
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t5 : ((446990787677/1000000000000 : ℚ) : ℝ) ≤ stT242 5 := by
  have hc : ((499751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446990787677/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((499751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c6 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((248501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136951/5000000) (δ := 12197/1000000000) (ψ := -1089/25000) 242 69
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t6 : ((1014449828457/2500000000000 : ℚ) : ℝ) ≤ stT242 6 := by
  have hc : ((496977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1014449828457/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((496977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c7 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((959639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5568/78125) (δ := 153/12500000) (ψ := -1089/25000) 242 75
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t7 : ((906726201579/2500000000000 : ℚ) : ℝ) ≤ stT242 7 := by
  have hc : ((959589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((906726201579/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((959589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c8 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((408793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191747/1250000) (δ := 12227/1000000000) (ψ := -1089/25000) 242 80
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t8 : ((22581449271/78125000000 : ℚ) : ℝ) ≤ stT242 8 := by
  have hc : ((12774/15625 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22581449271/78125000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((12774/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c9 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-332709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45977/80000) (δ := 757/62500000) (ψ := -1089/25000) 242 85
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t9 : ((-277278388789/1250000000000 : ℚ) : ℝ) ≤ stT242 9 := by
  have hc : ((-166367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277278388789/1250000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-166367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c10 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-177799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1208969/2500000) (δ := 12263/1000000000) (ψ := -1089/25000) 242 89
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t10 : ((-8786389423/78125000000 : ℚ) : ℝ) ≤ stT242 10 := by
  have hc : ((-5557/15625 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8786389423/78125000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-5557/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c11 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-652111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2851453/5000000) (δ := 6131/500000000) (ψ := -1089/25000) 242 92
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t11 : ((-983169880677/5000000000000 : ℚ) : ℝ) ≤ stT242 11 := by
  have hc : ((-652161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-983169880677/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-652161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c12 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-44431/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89741/200000) (δ := 12291/1000000000) (ψ := -1089/25000) 242 96
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t12 : ((-4009067051/62500000000 : ℚ) : ℝ) ≤ stT242 12 := by
  have hc : ((-44441/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4009067051/62500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-44441/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c13 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((292417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3185107/10000000) (δ := 12191/1000000000) (ψ := -1089/25000) 242 99
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t13 : ((1621759749/20000000000 : ℚ) : ℝ) ≤ stT242 13 := by
  have hc : ((292367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1621759749/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((292367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c14 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-579949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5473657/10000000) (δ := 12269/1000000000) (ψ := -1089/25000) 242 102
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t14 : ((-1550112867387/10000000000000 : ℚ) : ℝ) ≤ stT242 14 := by
  have hc : ((-579999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1550112867387/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-579999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c15 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-361291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4851121/10000000) (δ := 2451/200000000) (ψ := -1089/25000) 242 104
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t15 : ((-932978487249/10000000000000 : ℚ) : ℝ) ≤ stT242 15 := by
  have hc : ((-361341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-932978487249/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-361341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c16 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((276361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100843/312500) (δ := 12133/1000000000) (ψ := -1089/25000) 242 107
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t16 : ((276311/4000000 : ℚ) : ℝ) ≤ stT242 16 := by
  have hc : ((276311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276311/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((276311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c17 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((686601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2034981/10000000) (δ := 3071/250000000) (ψ := -1089/25000) 242 109
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t17 : ((416282646789/2500000000000 : ℚ) : ℝ) ≤ stT242 17 := by
  have hc : ((686551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416282646789/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((686551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c18 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-243721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2599943/5000000) (δ := 2421/200000000) (ψ := -1089/25000) 242 111
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t18 : ((-287257464079/2500000000000 : ℚ) : ℝ) ≤ stT242 18 := by
  have hc : ((-121873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287257464079/2500000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-121873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c19 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-26743/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1298923/2000000) (δ := 1229/100000000) (ψ := -1089/25000) 242 113
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t19 : ((-490850016127/2500000000000 : ℚ) : ℝ) ≤ stT242 19 := by
  have hc : ((-427913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490850016127/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-427913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c20 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-383341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1222227/2000000) (δ := 3069/250000000) (ψ := -1089/25000) 242 115
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t20 : ((-107154055611/625000000000 : ℚ) : ℝ) ≤ stT242 20 := by
  have hc : ((-191683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107154055611/625000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-191683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c21 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-57133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26333/62500) (δ := 6071/500000000) (ψ := -1089/25000) 242 117
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t21 : ((-62364493641/2500000000000 : ℚ) : ℝ) ≤ stT242 21 := by
  have hc : ((-28579/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62364493641/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-28579/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c22 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((464927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941953/10000000) (δ := 12247/1000000000) (ψ := -1089/25000) 242 119
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t22 : ((495587159157/2500000000000 : ℚ) : ℝ) ≤ stT242 22 := by
  have hc : ((232451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((495587159157/2500000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((232451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c23 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((1381/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1790317/5000000) (δ := 1217/100000000) (ψ := -1089/25000) 242 121
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t23 : ((719635323/25000000000 : ℚ) : ℝ) ≤ stT242 23 := by
  have hc : ((2761/20000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((719635323/25000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((2761/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c24 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-848523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6459961/10000000) (δ := 12277/1000000000) (ψ := -1089/25000) 242 122
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t24 : ((-866071423833/5000000000000 : ℚ) : ℝ) ≤ stT242 24 := by
  have hc : ((-848573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866071423833/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-848573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c25 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((994653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8083/312500) (δ := 12111/1000000000) (ψ := -1089/25000) 242 124
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t25 : ((994603/5000000 : ℚ) : ℝ) ≤ stT242 25 := by
  have hc : ((994603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((994603/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((994603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c26 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-499661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 485119/625000) (δ := 3051/250000000) (ψ := -1089/25000) 242 125
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t26 : ((-244991298783/1250000000000 : ℚ) : ℝ) ≤ stT242 26 := by
  have hc : ((-249843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244991298783/1250000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-249843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c27 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((946541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -821141/10000000) (δ := 1219/100000000) (ψ := -1089/25000) 242 127
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t27 : ((3643043859/20000000000 : ℚ) : ℝ) ≤ stT242 27 := by
  have hc : ((946491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3643043859/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((946491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c28 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-579851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2736677/5000000) (δ := 12283/1000000000) (ψ := -1089/25000) 242 128
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t28 : ((-1095910247523/10000000000000 : ℚ) : ℝ) ≤ stT242 28 := by
  have hc : ((-579901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1095910247523/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-579901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c29 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-308997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294521/625000) (δ := 3067/250000000) (ψ := -1089/25000) 242 130
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t29 : ((-286943031419/5000000000000 : ℚ) : ℝ) ≤ stT242 29 := by
  have hc : ((-309047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286943031419/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-309047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c30 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((19987/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90109/10000000) (δ := 6121/500000000) (ψ := -1089/25000) 242 131
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t30 : ((18244629813/100000000000 : ℚ) : ℝ) ≤ stT242 30 := by
  have hc : ((9993/10000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18244629813/100000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((9993/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c31 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-116949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844007/2000000) (δ := 12149/1000000000) (ψ := -1089/25000) 242 132
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t31 : ((-105068260973/5000000000000 : ℚ) : ℝ) ≤ stT242 31 := by
  have hc : ((-116999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105068260973/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-116999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c32 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-199713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1544007/2000000) (δ := 12147/1000000000) (ψ := -1089/25000) 242 133
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t32 : ((-353063728541/2000000000000 : ℚ) : ℝ) ≤ stT242 32 := by
  have hc : ((-199723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353063728541/2000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-199723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c33 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-222347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5079073/10000000) (δ := 12271/1000000000) (ψ := -1089/25000) 242 135
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t33 : ((-96775015761/1250000000000 : ℚ) : ℝ) ≤ stT242 33 := by
  have hc : ((-55593/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96775015761/1250000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-55593/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c34 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((462141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681493/2500000) (δ := 489/40000000) (ψ := -1089/25000) 242 136
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t34 : ((158495826727/2000000000000 : ℚ) : ℝ) ≤ stT242 34 := by
  have hc : ((462091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158495826727/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((462091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c35 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((93639/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -896497/10000000) (δ := 2457/200000000) (ψ := -1089/25000) 242 137
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t35 : ((19783787409/125000000000 : ℚ) : ℝ) ≤ stT242 35 := by
  have hc : ((46817/50000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19783787409/125000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((46817/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c36 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((984627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 219467/5000000) (δ := 381/31250000) (ψ := -1089/25000) 242 138
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t36 : ((820480505141/5000000000000 : ℚ) : ℝ) ≤ stT242 36 := by
  have hc : ((984577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((820480505141/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((984577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c37 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((866351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653683/5000000) (δ := 12299/1000000000) (ψ := -1089/25000) 242 139
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t37 : ((1424189314689/10000000000000 : ℚ) : ℝ) ≤ stT242 37 := by
  have hc : ((866301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1424189314689/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((866301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c38 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((192259/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1733663/10000000) (δ := 3049/250000000) (ψ := -1089/25000) 242 140
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t38 : ((311864963751/2500000000000 : ℚ) : ℝ) ≤ stT242 38 := by
  have hc : ((384493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311864963751/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((384493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c39 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((191797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1740877/10000000) (δ := 12289/1000000000) (ψ := -1089/25000) 242 141
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t39 : ((614201751889/5000000000000 : ℚ) : ℝ) ≤ stT242 39 := by
  have hc : ((383569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614201751889/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((383569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c40 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((857671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1350183/10000000) (δ := 6091/500000000) (ψ := -1089/25000) 242 142
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t40 : ((678008576349/5000000000000 : ℚ) : ℝ) ≤ stT242 40 := by
  have hc : ((857621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((678008576349/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((857621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c41 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((486547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 581243/10000000) (δ := 379/31250000) (ψ := -1089/25000) 242 143
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t41 : ((379909704357/2500000000000 : ℚ) : ℝ) ≤ stT242 41 := by
  have hc : ((243261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379909704357/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((243261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c42 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((9761/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68459/1250000) (δ := 2447/200000000) (ψ := -1089/25000) 242 144
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t42 : ((30121547193/200000000000 : ℚ) : ℝ) ≤ stT242 42 := by
  have hc : ((19521/20000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30121547193/200000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((19521/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c43 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((691037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2019683/10000000) (δ := 12143/1000000000) (ψ := -1089/25000) 242 145
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t43 : ((210748962039/2000000000000 : ℚ) : ℝ) ≤ stT242 43 := by
  have hc : ((690987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210748962039/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((690987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c44 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((43183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3818999/10000000) (δ := 12153/1000000000) (ψ := -1089/25000) 242 146
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t44 : ((16256353237/2500000000000 : ℚ) : ℝ) ≤ stT242 44 := by
  have hc : ((43133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16256353237/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((43133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c45 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-14369/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2965459/5000000) (δ := 12157/1000000000) (ψ := -1089/25000) 242 147
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t45 : ((-267769143/2500000000 : ℚ) : ℝ) ≤ stT242 45 := by
  have hc : ((-1437/2000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267769143/2500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-1437/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c46 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-196207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1841579/2500000) (δ := 6123/500000000) (ψ := -1089/25000) 242 147
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t46 : ((-14465313457/100000000000 : ℚ) : ℝ) ≤ stT242 46 := by
  have hc : ((-196217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14465313457/100000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-196217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c47 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-292719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 933933/2000000) (δ := 1533/125000000) (ψ := -1089/25000) 242 148
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t47 : ((-8540950037/200000000000 : ℚ) : ℝ) ≤ stT242 47 := by
  have hc : ((-292769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8540950037/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-292769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c48 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((388911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26547/156250) (δ := 1529/125000000) (ψ := -1089/25000) 242 149
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t48 : ((2245233321/20000000000 : ℚ) : ℝ) ≤ stT242 48 := by
  have hc : ((194443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2245233321/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((194443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c49 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((408751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1534339/10000000) (δ := 97/8000000) (ψ := -1089/25000) 242 150
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t49 : ((291947055273/2500000000000 : ℚ) : ℝ) ≤ stT242 49 := by
  have hc : ((204363/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291947055273/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((204363/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c50 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-211633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627451/1250000) (δ := 6093/500000000) (ψ := -1089/25000) 242 151
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t50 : ((-74832426703/1250000000000 : ℚ) : ℝ) ≤ stT242 50 := by
  have hc : ((-105829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74832426703/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-105829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c51 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-936877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1392193/2000000) (δ := 6093/500000000) (ψ := -1089/25000) 242 151
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t51 : ((-1311961076487/10000000000000 : ℚ) : ℝ) ≤ stT242 51 := by
  have hc : ((-936927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1311961076487/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-936927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c52 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((362003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375119/1250000) (δ := 1211/100000000) (ψ := -1089/25000) 242 152
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t52 : ((2007753291/40000000000 : ℚ) : ℝ) ≤ stT242 52 := by
  have hc : ((361953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2007753291/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((361953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c53 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((445071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23657/200000) (δ := 61/5000000) (ψ := -1089/25000) 242 153
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t53 : ((61131741083/500000000000 : ℚ) : ℝ) ≤ stT242 53 := by
  have hc : ((222523/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61131741083/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((222523/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c54 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-76841/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5582093/10000000) (δ := 12107/1000000000) (ψ := -1089/25000) 242 154
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t54 : ((-104575889523/1250000000000 : ℚ) : ℝ) ≤ stT242 54 := by
  have hc : ((-307389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104575889523/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-307389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c55 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-118933/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689889/1250000) (δ := 1537/125000000) (ψ := -1089/25000) 242 154
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t55 : ((-400956853/5000000000 : ℚ) : ℝ) ≤ stT242 55 := by
  have hc : ((-118943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400956853/5000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-118943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c56 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((959679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 356171/5000000) (δ := 6107/500000000) (ψ := -1089/25000) 242 155
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t56 : ((641178995237/5000000000000 : ℚ) : ℝ) ≤ stT242 56 := by
  have hc : ((959629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((641178995237/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((959629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c57 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-143651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1071841/2500000) (δ := 12281/1000000000) (ψ := -1089/25000) 242 156
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t57 : ((-190336716633/10000000000000 : ℚ) : ℝ) ≤ stT242 57 := by
  have hc : ((-143701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190336716633/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-143701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c58 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-39873/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 249387/400000) (δ := 12281/1000000000) (ψ := -1089/25000) 242 156
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t58 : ((-20943649363/200000000000 : ℚ) : ℝ) ≤ stT242 58 := by
  have hc : ((-79751/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20943649363/200000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-79751/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c59 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((940217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108603/1250000) (δ := 6087/500000000) (ψ := -1089/25000) 242 157
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t59 : ((1223993075463/10000000000000 : ℚ) : ℝ) ≤ stT242 59 := by
  have hc : ((940167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1223993075463/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((940167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c60 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-29317/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1167711/2500000) (δ := 12267/1000000000) (ψ := -1089/25000) 242 158
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t60 : ((-3785455539/100000000000 : ℚ) : ℝ) ≤ stT242 60 := by
  have hc : ((-14661/50000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3785455539/100000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-14661/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c61 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-531997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5329383/10000000) (δ := 1517/125000000) (ψ := -1089/25000) 242 158
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t61 : ((-681216485343/10000000000000 : ℚ) : ℝ) ≤ stT242 61 := by
  have hc : ((-532047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-681216485343/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-532047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c62 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((976679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270489/5000000) (δ := 19/1562500) (ψ := -1089/25000) 242 159
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t62 : ((1240319806629/10000000000000 : ℚ) : ℝ) ≤ stT242 62 := by
  have hc : ((976629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240319806629/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((976629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c63 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-870729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6568699/10000000) (δ := 243/20000000) (ψ := -1089/25000) 242 160
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t63 : ((-548539394039/5000000000000 : ℚ) : ℝ) ≤ stT242 63 := by
  have hc : ((-870779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548539394039/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-870779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c64 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((188793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1479511/5000000) (δ := 12253/1000000000) (ψ := -1089/25000) 242 160
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t64 : ((5899/125000 : ℚ) : ℝ) ≤ stT242 64 := by
  have hc : ((5899/15625 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5899/125000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((5899/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c65 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((221387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33689/100000) (δ := 6073/500000000) (ψ := -1089/25000) 242 161
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t65 : ((274534683939/10000000000000 : ℚ) : ℝ) ≤ stT242 65 := by
  have hc : ((221337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274534683939/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((221337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c66 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-700701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2933969/5000000) (δ := 12257/1000000000) (ψ := -1089/25000) 242 161
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t66 : ((-172512983433/2000000000000 : ℚ) : ℝ) ≤ stT242 66 := by
  have hc : ((-700751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172512983433/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-700751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c67 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((478133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46381/625000) (δ := 2433/200000000) (ψ := -1089/25000) 242 162
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t67 : ((73012709369/625000000000 : ℚ) : ℝ) ≤ stT242 67 := by
  have hc : ((119527/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73012709369/625000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((119527/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c68 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-989241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1871731/2500000) (δ := 12131/1000000000) (ψ := -1089/25000) 242 163
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t68 : ((-1199692420589/10000000000000 : ℚ) : ℝ) ≤ stT242 68 := by
  have hc : ((-989291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1199692420589/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-989291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c69 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((858663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26907/200000) (δ := 12131/1000000000) (ψ := -1089/25000) 242 163
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t69 : ((516824064477/5000000000000 : ℚ) : ℝ) ≤ stT242 69 := by
  have hc : ((858613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516824064477/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((858613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c70 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-31911/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113149/200000) (δ := 191/15625000) (ψ := -1089/25000) 242 164
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t70 : ((-76287881383/1000000000000 : ℚ) : ℝ) ≤ stT242 70 := by
  have hc : ((-63827/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76287881383/1000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-63827/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c71 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((195217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2924233/10000000) (δ := 191/15625000) (ψ := -1089/25000) 242 164
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t71 : ((28956269619/625000000000 : ℚ) : ℝ) ≤ stT242 71 := by
  have hc : ((24399/62500 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28956269619/625000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((24399/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c72 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-78677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2161009/5000000) (δ := 6143/500000000) (ψ := -1089/25000) 242 165
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t72 : ((-2898476607/156250000000 : ℚ) : ℝ) ≤ stT242 72 := by
  have hc : ((-39351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2898476607/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-39351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c73 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-7673/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251433/625000) (δ := 12117/1000000000) (ψ := -1089/25000) 242 165
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t73 : ((-2248068849/500000000000 : ℚ) : ℝ) ≤ stT242 73 := by
  have hc : ((-7683/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2248068849/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-7683/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c74 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((11763/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3453647/10000000) (δ := 12193/1000000000) (ψ := -1089/25000) 242 166
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t74 : ((27341144901/1250000000000 : ℚ) : ℝ) ≤ stT242 74 := by
  have hc : ((94079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27341144901/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((94079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c75 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-145913/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72927/156250) (δ := 1221/100000000) (ψ := -1089/25000) 242 166
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t75 : ((-84257377269/2500000000000 : ℚ) : ℝ) ≤ stT242 75 := by
  have hc : ((-72969/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84257377269/2500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-72969/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c76 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((352163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3027289/10000000) (δ := 12103/1000000000) (ψ := -1089/25000) 242 167
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t76 : ((201950537907/5000000000000 : ℚ) : ℝ) ≤ stT242 76 := by
  have hc : ((352113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201950537907/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((352113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c77 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-372533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1220333/2500000) (δ := 123/10000000) (ψ := -1089/25000) 242 167
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t77 : ((-212298911149/5000000000000 : ℚ) : ℝ) ≤ stT242 77 := by
  have hc : ((-372583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212298911149/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-372583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c78 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((177431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120803/400000) (δ := 2439/200000000) (ψ := -1089/25000) 242 168
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t78 : ((100436366731/2500000000000 : ℚ) : ℝ) ≤ stT242 78 := by
  have hc : ((88703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100436366731/2500000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((88703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c79 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-5987/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 234351/500000) (δ := 2439/200000000) (ψ := -1089/25000) 242 168
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t79 : ((-52633023/1562500000 : ℚ) : ℝ) ≤ stT242 79 := by
  have hc : ((-1497/5000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52633023/1562500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-1497/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c80 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((6407/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3410769/10000000) (δ := 2423/200000000) (ψ := -1089/25000) 242 169
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t80 : ((114583848071/5000000000000 : ℚ) : ℝ) ≤ stT242 80 := by
  have hc : ((102487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114583848071/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((102487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c81 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-71081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4104843/10000000) (δ := 24/1953125) (ψ := -1089/25000) 242 169
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t81 : ((-9879313459/1250000000000 : ℚ) : ℝ) ≤ stT242 81 := by
  have hc : ((-71131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9879313459/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-71131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c82 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-20183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4179709/10000000) (δ := 6111/500000000) (ψ := -1089/25000) 242 170
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t82 : ((-5574863247/500000000000 : ℚ) : ℝ) ≤ stT242 82 := by
  have hc : ((-20193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5574863247/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-20193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c83 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((304393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1576869/5000000) (δ := 6111/500000000) (ψ := -1089/25000) 242 170
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t83 : ((167029829603/5000000000000 : ℚ) : ℝ) ≤ stT242 83 := by
  have hc : ((304343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167029829603/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((304343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c84 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-262479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1061731/2000000) (δ := 12137/500000000) (ψ := -1089/25000) 242 171
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t84 : ((-3580193617/62500000000 : ℚ) : ℝ) ≤ stT242 84 := by
  have hc : ((-32813/62500 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3580193617/62500000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-32813/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c85 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((184537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1851187/10000000) (δ := 6137/500000000) (ψ := -1089/25000) 242 171
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t85 : ((100072433987/1250000000000 : ℚ) : ℝ) ≤ stT242 85 := by
  have hc : ((369049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100072433987/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((369049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c86 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-909251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -847587/1250000) (δ := 12167/1000000000) (ψ := -1089/25000) 242 172
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t86 : ((-122565591091/1250000000000 : ℚ) : ℝ) ≤ stT242 86 := by
  have hc : ((-909301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122565591091/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-909301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c87 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((996351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213649/10000000) (δ := 3059/250000000) (ψ := -1089/25000) 242 172
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t87 : ((66759141107/625000000000 : ℚ) : ℝ) ≤ stT242 87 := by
  have hc : ((996301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66759141107/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((996301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c88 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-958133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1782003/2500000) (δ := 12167/1000000000) (ψ := -1089/25000) 242 172
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t88 : ((-255356727683/2500000000000 : ℚ) : ℝ) ≤ stT242 88 := by
  have hc : ((-958183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255356727683/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-958183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c89 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((766449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871877/5000000) (δ := 12259/1000000000) (ψ := -1089/25000) 242 173
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t89 : ((812380640803/10000000000000 : ℚ) : ℝ) ≤ stT242 89 := by
  have hc : ((766399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((812380640803/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((766399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c90 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-52749/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5016093/10000000) (δ := 759/62500000) (ψ := -1089/25000) 242 173
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t90 : ((-222435758953/5000000000000 : ℚ) : ℝ) ≤ stT242 90 := by
  have hc : ((-211021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222435758953/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-211021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c91 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-31883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4006711/10000000) (δ := 24251/1000000000) (ψ := -1089/25000) 242 174
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t91 : ((-6694976981/2000000000000 : ℚ) : ℝ) ≤ stT242 91 := by
  have hc : ((-31933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6694976981/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-31933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c92 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((504369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651341/2500000) (δ := 1519/125000000) (ψ := -1089/25000) 242 174
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t92 : ((131447217117/2500000000000 : ℚ) : ℝ) ≤ stT242 92 := by
  have hc : ((504319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131447217117/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((504319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c93 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-869409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312401/2000000) (δ := 2449/200000000) (ψ := -1089/25000) 242 175
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t93 : ((-112698406121/1250000000000 : ℚ) : ℝ) ≤ stT242 93 := by
  have hc : ((-869459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112698406121/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-869459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c94 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((999333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22837/2500000) (δ := 6079/500000000) (ψ := -1089/25000) 242 175
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t94 : ((1030681471143/10000000000000 : ℚ) : ℝ) ≤ stT242 94 := by
  have hc : ((999283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1030681471143/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((999283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c95 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-163093/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3155411/5000000) (δ := 2449/200000000) (ψ := -1089/25000) 242 175
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t95 : ((-167340252837/2000000000000 : ℚ) : ℝ) ≤ stT242 95 := by
  have hc : ((-163103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167340252837/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-163103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c96 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((339133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -765501/2500000) (δ := 2453/200000000) (ψ := -1089/25000) 242 176
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t96 : ((17303744573/500000000000 : ℚ) : ℝ) ≤ stT242 96 := by
  have hc : ((339083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17303744573/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((339083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c97 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((70961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320749/1000000) (δ := 2453/200000000) (ψ := -1089/25000) 242 176
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t97 : ((72037275681/2500000000000 : ℚ) : ℝ) ≤ stT242 97 := by
  have hc : ((141897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72037275681/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((141897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c98 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-405927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6295291/10000000) (δ := 3043/250000000) (ψ := -1089/25000) 242 177
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t98 : ((-6407400479/78125000000 : ℚ) : ℝ) ≤ stT242 98 := by
  have hc : ((-12686/15625 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6407400479/78125000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-12686/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c99 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((499063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153089/10000000) (δ := 3043/250000000) (ψ := -1089/25000) 242 177
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t99 : ((250775827203/2500000000000 : ℚ) : ℝ) ≤ stT242 99 := by
  have hc : ((249519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250775827203/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((249519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c100 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-358727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2963671/5000000) (δ := 12231/1000000000) (ψ := -1089/25000) 242 177
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t100 : ((-11211/156250 : ℚ) : ℝ) ≤ stT242 100 := by
  have hc : ((-11211/15625 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11211/156250 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-11211/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c101 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((1039/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3760629/10000000) (δ := 3031/250000000) (ψ := -1089/25000) 242 178
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t101 : ((33058114251/5000000000000 : ℚ) : ℝ) ≤ stT242 101 := by
  have hc : ((33223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33058114251/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((33223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c102 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((637147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2200013/10000000) (δ := 12279/1000000000) (ψ := -1089/25000) 242 178
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t102 : ((630819683259/10000000000000 : ℚ) : ℝ) ≤ stT242 102 := by
  have hc : ((637097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630819683259/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((637097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c103 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-199013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760551/1000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 179
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t103 : ((-19610333259/200000000000 : ℚ) : ℝ) ≤ stT242 103 := by
  have hc : ((-199023/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19610333259/200000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-199023/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c104 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((762243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760061/10000000) (δ := 1527/125000000) (ψ := -1089/25000) 242 179
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t104 : ((37369560597/500000000000 : ℚ) : ℝ) ≤ stT242 104 := by
  have hc : ((762193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37369560597/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((762193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c105 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-40987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4029487/10000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 179
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t105 : ((-40048049337/10000000000000 : ℚ) : ℝ) ≤ stT242 105 := by
  have hc : ((-41037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40048049337/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-41037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c106 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-361021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5943863/10000000) (δ := 12109/1000000000) (ψ := -1089/25000) 242 180
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t106 : ((-87669731289/1250000000000 : ℚ) : ℝ) ≤ stT242 106 := by
  have hc : ((-180523/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87669731289/1250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-180523/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c107 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((99447/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131517/5000000) (δ := 12109/1000000000) (ψ := -1089/25000) 242 180
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t107 : ((3004192541/31250000000 : ℚ) : ℝ) ≤ stT242 107 := by
  have hc : ((49721/50000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3004192541/31250000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((49721/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c108 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-271989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2682459/5000000) (δ := 12109/1000000000) (ψ := -1089/25000) 242 180
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t108 : ((-130872871757/2500000000000 : ℚ) : ℝ) ≤ stT242 108 := by
  have hc : ((-136007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130872871757/2500000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-136007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c109 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-164859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383501/5000000) (δ := 12201/1000000000) (ψ := -1089/25000) 242 181
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t109 : ((-39482586767/1250000000000 : ℚ) : ℝ) ≤ stT242 109 := by
  have hc : ((-41221/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39482586767/1250000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-41221/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c110 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((954367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9477/125000) (δ := 6101/500000000) (ψ := -1089/25000) 242 181
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t110 : ((454952497727/5000000000000 : ℚ) : ℝ) ≤ stT242 110 := by
  have hc : ((954317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454952497727/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((954317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c111 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-39857/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124667/200000) (δ := 12201/1000000000) (ψ := -1089/25000) 242 181
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t111 : ((-37832963301/500000000000 : ℚ) : ℝ) ≤ stT242 111 := by
  have hc : ((-79719/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37832963301/500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-79719/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c112 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-48629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4048611/10000000) (δ := 2459/200000000) (ψ := -1089/25000) 242 182
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t112 : ((-2874835703/625000000000 : ℚ) : ℝ) ≤ stT242 112 := by
  have hc : ((-48679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2874835703/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-48679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c113 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((17239/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 664617/5000000) (δ := 2459/200000000) (ψ := -1089/25000) 242 182
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t113 : ((101350821/1250000000 : ℚ) : ℝ) ≤ stT242 113 := by
  have hc : ((8619/10000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101350821/1250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((8619/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c114 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-888039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6659647/10000000) (δ := 2459/200000000) (ψ := -1089/25000) 242 182
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t114 : ((-415885862077/5000000000000 : ℚ) : ℝ) ≤ stT242 114 := by
  have hc : ((-888089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415885862077/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-888089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c115 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((3249/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3764427/10000000) (δ := 2443/200000000) (ψ := -1089/25000) 242 183
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t115 : ((756843559/125000000000 : ℚ) : ℝ) ≤ stT242 115 := by
  have hc : ((6493/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((756843559/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((6493/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c116 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((415619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473663/10000000) (δ := 2443/200000000) (ψ := -1089/25000) 242 183
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t116 : ((48233631843/625000000000 : ℚ) : ℝ) ≤ stT242 116 := by
  have hc : ((207797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48233631843/625000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((207797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c117 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-444681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3333431/5000000) (δ := 2443/200000000) (ψ := -1089/25000) 242 183
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t117 : ((-205565570853/2500000000000 : ℚ) : ℝ) ≤ stT242 117 := by
  have hc : ((-222353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205565570853/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-222353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c118 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((2789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121629/312500) (δ := 12123/1000000000) (ψ := -1089/25000) 242 184
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t118 : ((1279137573/1000000000000 : ℚ) : ℝ) ≤ stT242 118 := by
  have hc : ((2779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1279137573/1000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((2779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c119 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((884517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606673/5000000) (δ := 12123/1000000000) (ψ := -1089/25000) 242 184
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t119 : ((405394564983/5000000000000 : ℚ) : ℝ) ≤ stT242 119 := by
  have hc : ((884467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((405394564983/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((884467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c120 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-201841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6276167/10000000) (δ := 307/25000000) (ψ := -1089/25000) 242 184
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t120 : ((-368532412797/5000000000000 : ℚ) : ℝ) ≤ stT242 120 := by
  have hc : ((-403707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368532412797/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-403707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c121 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-38481/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2205511/5000000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 185
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t121 : ((-34991821681/2000000000000 : ℚ) : ℝ) ≤ stT242 121 := by
  have hc : ((-38491/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34991821681/2000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-38491/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c122 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((487131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568431/10000000) (δ := 1223/100000000) (ψ := -1089/25000) 242 185
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t122 : ((220502413421/2500000000000 : ℚ) : ℝ) ≤ stT242 122 := by
  have hc : ((243553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220502413421/2500000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((243553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c123 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-147709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5507227/10000000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 185
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t123 : ((-26639208981/500000000000 : ℚ) : ℝ) ≤ stT242 123 := by
  have hc : ((-295443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26639208981/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-295443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c124 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-261333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -530193/1000000) (δ := 12137/1000000000) (ψ := -1089/25000) 242 186
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t124 : ((-117353270333/2500000000000 : ℚ) : ℝ) ≤ stT242 124 := by
  have hc : ((-130679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117353270333/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-130679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c125 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((49219/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -442449/10000000) (δ := 12137/1000000000) (ψ := -1089/25000) 242 186
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t125 : ((88041132891/1000000000000 : ℚ) : ℝ) ≤ stT242 125 := by
  have hc : ((98433/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88041132891/1000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((98433/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c126 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-179549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547289/1250000) (δ := 12137/1000000000) (ψ := -1089/25000) 242 186
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t126 : ((-159999540729/10000000000000 : ℚ) : ℝ) ≤ stT242 126 := by
  have hc : ((-179599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159999540729/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-179599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c127 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-866441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3273533/5000000) (δ := 12159/1000000000) (ψ := -1089/25000) 242 187
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t127 : ((-768886854287/10000000000000 : ℚ) : ℝ) ≤ stT242 127 := by
  have hc : ((-866491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-768886854287/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-866491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c128 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((11739/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180193/1000000) (δ := 12159/1000000000) (ψ := -1089/25000) 242 187
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t128 : ((332006784109/5000000000000 : ℚ) : ℝ) ≤ stT242 128 := by
  have hc : ((375623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332006784109/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((375623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c129 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((99257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2906301/10000000) (δ := 12159/1000000000) (ψ := -1089/25000) 242 187
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t129 : ((3495192801/100000000000 : ℚ) : ℝ) ≤ stT242 129 := by
  have hc : ((198489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3495192801/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((198489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c130 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-496959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7578111/10000000) (δ := 12159/1000000000) (ψ := -1089/25000) 242 187
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t130 : ((-54485536257/625000000000 : ℚ) : ℝ) ≤ stT242 130 := by
  have hc : ((-62123/62500 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54485536257/625000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-62123/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c131 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((172411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1746899/5000000) (δ := 3063/250000000) (ψ := -1089/25000) 242 188
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t131 : ((18824061893/1250000000000 : ℚ) : ℝ) ≤ stT242 131 := by
  have hc : ((172361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18824061893/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((172361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c132 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((451779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221397/2000000) (δ := 3063/250000000) (ψ := -1089/25000) 242 188
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t132 : ((49150157569/625000000000 : ℚ) : ℝ) ≤ stT242 132 := by
  have hc : ((225877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49150157569/625000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((225877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c133 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-10047/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5673041/10000000) (δ := 3063/250000000) (ψ := -1089/25000) 242 188
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t133 : ((-27880101119/500000000000 : ℚ) : ℝ) ≤ stT242 133 := by
  have hc : ((-321529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27880101119/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-321529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c134 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-73687/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5503079/10000000) (δ := 4869/200000000) (ψ := -1089/25000) 242 189
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t134 : ((-254645256737/5000000000000 : ℚ) : ℝ) ≤ stT242 134 := by
  have hc : ((-294773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254645256737/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-294773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c135 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((920291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -502467/5000000) (δ := 2429/200000000) (ψ := -1089/25000) 242 189
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t135 : ((396008229771/5000000000000 : ℚ) : ℝ) ≤ stT242 135 := by
  have hc : ((920241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((396008229771/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((920241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c136 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((185701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3460027/10000000) (δ := 6129/500000000) (ψ := -1089/25000) 242 189
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t136 : ((39798561823/2500000000000 : ℚ) : ℝ) ≤ stT242 136 := by
  have hc : ((185651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39798561823/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((185651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c137 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-499941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907823/5000000) (δ := 6083/500000000) (ψ := -1089/25000) 242 190
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t137 : ((-106787487957/1250000000000 : ℚ) : ℝ) ≤ stT242 137 := by
  have hc : ((-249983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106787487957/1250000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-249983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c138 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((50777/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3415663/10000000) (δ := 12237/1000000000) (ψ := -1089/25000) 242 190
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t138 : ((10803396303/625000000000 : ℚ) : ℝ) ≤ stT242 138 := by
  have hc : ((101529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10803396303/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((101529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c139 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((232069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952619/10000000) (δ := 6083/500000000) (ψ := -1089/25000) 242 190
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t139 : ((98413769311/1250000000000 : ℚ) : ℝ) ≤ stT242 139 := by
  have hc : ((464113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98413769311/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((464113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c140 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-259221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5289561/10000000) (δ := 12237/1000000000) (ψ := -1089/25000) 242 190
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t140 : ((-21910305313/500000000000 : ℚ) : ℝ) ≤ stT242 140 := by
  have hc : ((-129623/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21910305313/500000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-129623/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c141 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-767001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48899/80000) (δ := 1213/100000000) (ψ := -1089/25000) 242 191
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t141 : ((-80746691719/1250000000000 : ℚ) : ℝ) ≤ stT242 141 := by
  have hc : ((-767051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80746691719/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-767051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c142 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((18551/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1836719/10000000) (δ := 1213/100000000) (ψ := -1089/25000) 242 191
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t142 : ((62266391019/1000000000000 : ℚ) : ℝ) ≤ stT242 142 := by
  have hc : ((74199/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62266391019/1000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((74199/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c143 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((570591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2408929/10000000) (δ := 1213/100000000) (ψ := -1089/25000) 242 191
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t143 : ((238555173461/5000000000000 : ℚ) : ℝ) ≤ stT242 143 := by
  have hc : ((570541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238555173461/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((570541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c144 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-881569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1656233/2500000) (δ := 1213/100000000) (ψ := -1089/25000) 242 191
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t144 : ((-367341543873/5000000000000 : ℚ) : ℝ) ≤ stT242 144 := by
  have hc : ((-881619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367341543873/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-881619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c145 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-378019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4896129/10000000) (δ := 12223/1000000000) (ψ := -1089/25000) 242 192
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t145 : ((-62793858279/2000000000000 : ℚ) : ℝ) ≤ stT242 145 := by
  have hc : ((-378069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62793858279/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-378069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c146 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((956741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92253/1250000) (δ := 609/50000000) (ψ := -1089/25000) 242 192
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t146 : ((158352451011/2000000000000 : ℚ) : ℝ) ≤ stT242 146 := by
  have hc : ((956691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158352451011/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((956691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c147 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((106253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 678329/2000000) (δ := 12223/1000000000) (ψ := -1089/25000) 242 192
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t147 : ((10951920901/625000000000 : ℚ) : ℝ) ≤ stT242 147 := by
  have hc : ((26557/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10951920901/625000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((26557/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c148 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-494807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1873341/2500000) (δ := 609/50000000) (ψ := -1089/25000) 242 192
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t148 : ((-5084367873/62500000000 : ℚ) : ℝ) ≤ stT242 148 := by
  have hc : ((-30927/31250 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5084367873/62500000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-30927/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c149 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-10661/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4140469/10000000) (δ := 3029/250000000) (ψ := -1089/25000) 242 193
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t149 : ((-1092369069/156250000000 : ℚ) : ℝ) ≤ stT242 149 := by
  have hc : ((-42669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1092369069/156250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-42669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c150 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((499649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23421/2500000) (δ := 12287/1000000000) (ψ := -1089/25000) 242 193
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t150 : ((3187039043/39062500000 : ℚ) : ℝ) ≤ stT242 150 := by
  have hc : ((62453/62500 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3187039043/39062500000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((62453/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c151 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3926299/10000000) (δ := 12287/1000000000) (ψ := -1089/25000) 242 193
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t151 : ((46182469/2500000000000 : ℚ) : ℝ) ≤ stT242 151 := by
  have hc : ((227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46182469/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c152 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-499827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7788241/10000000) (δ := 6097/500000000) (ψ := -1089/25000) 242 194
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t152 : ((-25339622251/312500000000 : ℚ) : ℝ) ≤ stT242 152 := by
  have hc : ((-124963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25339622251/312500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-124963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c153 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((21189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1910507/5000000) (δ := 6097/500000000) (ψ := -1089/25000) 242 194
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t153 : ((1069379883/312500000000 : ℚ) : ℝ) ≤ stT242 153 := by
  have hc : ((5291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1069379883/312500000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((5291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c154 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((998841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120379/10000000) (δ := 12209/1000000000) (ψ := -1089/25000) 242 194
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t154 : ((402423880601/5000000000000 : ℚ) : ℝ) ≤ stT242 154 := by
  have hc : ((998791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402423880601/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((998791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c155 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-43687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2018121/5000000) (δ := 6097/500000000) (ψ := -1089/25000) 242 194
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t155 : ((-1756521657/500000000000 : ℚ) : ℝ) ≤ stT242 155 := by
  have hc : ((-43737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1756521657/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-43737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c156 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-499787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7781027/10000000) (δ := 6051/500000000) (ψ := -1089/25000) 242 195
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t156 : ((-100042494873/1250000000000 : ℚ) : ℝ) ≤ stT242 156 := by
  have hc : ((-124953/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100042494873/1250000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-124953/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c157 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((4717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957599/5000000) (δ := 6051/500000000) (ψ := -1089/25000) 242 195
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t157 : ((1862333681/5000000000000 : ℚ) : ℝ) ≤ stT242 157 := by
  have hc : ((4667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1862333681/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((4667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c158 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((999563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18483/2500000) (δ := 6051/500000000) (ψ := -1089/25000) 242 195
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t158 : ((795169563741/10000000000000 : ℚ) : ℝ) ≤ stT242 158 := by
  have hc : ((999513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((795169563741/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((999513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c159 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((18369/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1871567/5000000) (δ := 6051/500000000) (ψ := -1089/25000) 242 195
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t159 : ((29115281363/5000000000000 : ℚ) : ℝ) ≤ stT242 159 := by
  have hc : ((36713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29115281363/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((36713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c160 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-495967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3768121/5000000) (δ := 6051/500000000) (ψ := -1089/25000) 242 195
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t160 : ((-4901454943/62500000000 : ℚ) : ℝ) ≤ stT242 160 := by
  have hc : ((-61999/62500 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4901454943/62500000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-61999/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c161 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-23621/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4402269/10000000) (δ := 6097/500000000) (ψ := -1089/25000) 242 196
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t161 : ((-74483582499/5000000000000 : ℚ) : ℝ) ≤ stT242 161 := by
  have hc : ((-94509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74483582499/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-94509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c162 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((965759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656109/10000000) (δ := 6097/500000000) (ψ := -1089/25000) 242 196
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t162 : ((379366226433/5000000000000 : ℚ) : ℝ) ≤ stT242 162 := by
  have hc : ((965709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379366226433/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((965709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c163 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((84313/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3067001/10000000) (δ := 12209/1000000000) (ψ := -1089/25000) 242 196
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t163 : ((6602920963/250000000000 : ℚ) : ℝ) ≤ stT242 163 := by
  have hc : ((168601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6602920963/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((168601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c164 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-14172/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3383651/5000000) (δ := 12209/1000000000) (ψ := -1089/25000) 242 196
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t164 : ((-354146736701/5000000000000 : ℚ) : ℝ) ≤ stT242 164 := by
  have hc : ((-453529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354146736701/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-453529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c165 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-254641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5262867/10000000) (δ := 12287/1000000000) (ψ := -1089/25000) 242 197
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t165 : ((-99128613167/2500000000000 : ℚ) : ℝ) ≤ stT242 165 := by
  have hc : ((-127333/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99128613167/2500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-127333/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c166 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((160071/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64291/400000) (δ := 3029/250000000) (ψ := -1089/25000) 242 197
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t166 : ((2484626903/40000000000 : ℚ) : ℝ) ≤ stT242 166 := by
  have hc : ((160061/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2484626903/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((160061/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c167 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((10767/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 405283/2000000) (δ := 12287/1000000000) (ψ := -1089/25000) 242 197
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t167 : ((266596726137/5000000000000 : ℚ) : ℝ) ≤ stT242 167 := by
  have hc : ((344519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266596726137/5000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((344519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c168 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-79039/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2819163/5000000) (δ := 3029/250000000) (ψ := -1089/25000) 242 197
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t168 : ((-243939016577/5000000000000 : ℚ) : ℝ) ≤ stT242 168 := by
  have hc : ((-316181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243939016577/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-316181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c169 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-426273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6479083/10000000) (δ := 12223/1000000000) (ψ := -1089/25000) 242 198
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t169 : ((-163960818419/2500000000000 : ℚ) : ℝ) ≤ stT242 169 := by
  have hc : ((-213149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163960818419/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-213149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c170 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((79151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581953/2000000) (δ := 609/50000000) (ψ := -1089/25000) 242 198
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t170 : ((15174574481/500000000000 : ℚ) : ℝ) ≤ stT242 170 := by
  have hc : ((79141/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15174574481/500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((79141/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c171 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((19351/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 638621/10000000) (δ := 12223/1000000000) (ψ := -1089/25000) 242 198
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t171 : ((295946253/4000000000 : ℚ) : ℝ) ≤ stT242 171 := by
  have hc : ((387/400 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295946253/4000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((387/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c172 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-2987/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 833263/2000000) (δ := 609/50000000) (ψ := -1089/25000) 242 198
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t172 : ((-36460127781/5000000000000 : ℚ) : ℝ) ≤ stT242 172 := by
  have hc : ((-47817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36460127781/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-47817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c173 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-997397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7673561/10000000) (δ := 12223/1000000000) (ψ := -1089/25000) 242 198
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t173 : ((-379172494921/5000000000000 : ℚ) : ℝ) ≤ stT242 173 := by
  have hc : ((-997447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379172494921/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-997447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c174 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-24561/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1136841/2500000) (δ := 1213/100000000) (ψ := -1089/25000) 242 199
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t174 : ((-9311730017/500000000000 : ℚ) : ℝ) ≤ stT242 174 := by
  have hc : ((-12283/50000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9311730017/500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-12283/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c175 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((908081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1080291/10000000) (δ := 12273/1000000000) (ψ := -1089/25000) 242 199
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t175 : ((85800757221/1250000000000 : ℚ) : ℝ) ≤ stT242 175 := by
  have hc : ((908031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85800757221/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((908031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c176 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((584283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2366999/10000000) (δ := 12273/1000000000) (ψ := -1089/25000) 242 199
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t176 : ((220190991137/5000000000000 : ℚ) : ℝ) ≤ stT242 176 := by
  have hc : ((584233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220190991137/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((584233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c177 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-339767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724351/1250000) (δ := 12273/1000000000) (ψ := -1089/25000) 242 199
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t177 : ((-15962727339/312500000000 : ℚ) : ℝ) ≤ stT242 177 := by
  have hc : ((-21237/31250 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15962727339/312500000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-21237/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c178 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-428929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3252353/5000000) (δ := 6083/500000000) (ψ := -1089/25000) 242 200
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t178 : ((-40189343691/625000000000 : ℚ) : ℝ) ≤ stT242 178 := by
  have hc : ((-214477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40189343691/625000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-214477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c179 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((318997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557657/5000000) (δ := 12237/1000000000) (ψ := -1089/25000) 242 200
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t179 : ((47678430189/2000000000000 : ℚ) : ℝ) ≤ stT242 179 := by
  have hc : ((318947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47678430189/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((318947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c180 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((994797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255141/10000000) (δ := 12237/1000000000) (ψ := -1089/25000) 242 200
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t180 : ((148287930037/2000000000000 : ℚ) : ℝ) ≤ stT242 180 := by
  have hc : ((994747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148287930037/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((994747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c181 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((63831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1803481/5000000) (δ := 12237/1000000000) (ψ := -1089/25000) 242 200
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t181 : ((11856654241/1250000000000 : ℚ) : ℝ) ≤ stT242 181 := by
  have hc : ((31903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11856654241/1250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((31903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c182 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-933951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694027/1000000) (δ := 12237/1000000000) (ψ := -1089/25000) 242 200
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t182 : ((-553862593/8000000000 : ℚ) : ℝ) ≤ stT242 182 := by
  have hc : ((-934001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553862593/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-934001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c183 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-286533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1363149/2500000) (δ := 2429/200000000) (ψ := -1089/25000) 242 201
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t183 : ((-52957494469/1250000000000 : ℚ) : ℝ) ≤ stT242 183 := by
  have hc : ((-143279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52957494469/1250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-143279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c184 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((325371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538897/2500000) (δ := 2429/200000000) (ψ := -1089/25000) 242 201
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t184 : ((119923999657/2500000000000 : ℚ) : ℝ) ≤ stT242 184 := by
  have hc : ((162673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119923999657/2500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((162673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c185 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((180139/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280893/2500000) (δ := 6129/500000000) (ψ := -1089/25000) 242 201
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t185 : ((66216681303/1000000000000 : ℚ) : ℝ) ≤ stT242 185 := by
  have hc : ((180129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66216681303/1000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((180129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c186 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-182183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2192503/5000000) (δ := 6129/500000000) (ψ := -1089/25000) 242 201
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t186 : ((-33404948997/2500000000000 : ℚ) : ℝ) ≤ stT242 186 := by
  have hc : ((-182233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33404948997/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-182233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c187 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-497977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953627/1250000) (δ := 6129/500000000) (ψ := -1089/25000) 242 201
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t187 : ((-182087708273/2500000000000 : ℚ) : ℝ) ≤ stT242 187 := by
  have hc : ((-249001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182087708273/2500000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-249001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c188 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-361731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48523/100000) (δ := 3063/250000000) (ψ := -1089/25000) 242 202
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t188 : ((-10554237113/400000000000 : ℚ) : ℝ) ≤ stT242 188 := by
  have hc : ((-361781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10554237113/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-361781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c189 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((31671/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328543/2000000) (δ := 12151/1000000000) (ψ := -1089/25000) 242 202
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t189 : ((719868039/12500000000 : ℚ) : ℝ) ≤ stT242 189 := by
  have hc : ((31669/40000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((719868039/12500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((31669/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c190 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((813909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154987/1000000) (δ := 12151/1000000000) (ψ := -1089/25000) 242 202
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t190 : ((147608792971/2500000000000 : ℚ) : ℝ) ≤ stT242 190 := by
  have hc : ((813859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147608792971/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((813859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c191 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-157049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4725757/10000000) (δ := 12151/1000000000) (ψ := -1089/25000) 242 202
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t191 : ((-2273096391/100000000000 : ℚ) : ℝ) ≤ stT242 191 := by
  have hc : ((-78537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2273096391/100000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-78537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c192 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-999923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7822957/10000000) (δ := 3061/250000000) (ψ := -1089/25000) 242 203
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t192 : ((-90208564303/1250000000000 : ℚ) : ℝ) ≤ stT242 192 := by
  have hc : ((-999973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90208564303/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-999973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c193 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-296709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4680103/10000000) (δ := 3061/250000000) (ψ := -1089/25000) 242 203
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t193 : ((-26701484543/1250000000000 : ℚ) : ℝ) ≤ stT242 193 := by
  have hc : ((-296759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26701484543/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-296759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c194 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((813073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1553463/10000000) (δ := 3061/250000000) (ψ := -1089/25000) 242 203
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t194 : ((291858183517/5000000000000 : ℚ) : ℝ) ≤ stT242 194 := by
  have hc : ((813023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291858183517/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((813023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c195 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((812229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 389271/2500000) (δ := 3061/250000000) (ψ := -1089/25000) 242 203
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t195 : ((290806376203/5000000000000 : ℚ) : ℝ) ≤ stT242 195 := by
  have hc : ((812179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290806376203/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((812179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c196 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-35731/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116293/250000) (δ := 12159/1000000000) (ψ := -1089/25000) 242 203
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t196 : ((-51053234707/2500000000000 : ℚ) : ℝ) ≤ stT242 196 := by
  have hc : ((-142949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51053234707/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-142949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c197 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-998783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12369/16000) (δ := 3061/250000000) (ψ := -1089/25000) 242 203
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t197 : ((-711639546343/10000000000000 : ℚ) : ℝ) ≤ stT242 197 := by
  have hc : ((-998833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-711639546343/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-998833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c198 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-192321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4914041/10000000) (δ := 6133/500000000) (ψ := -1089/25000) 242 204
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t198 : ((-6834726591/250000000000 : ℚ) : ℝ) ≤ stT242 198 := by
  have hc : ((-96173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6834726591/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-96173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c199 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((734091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -466543/2500000) (δ := 6133/500000000) (ψ := -1089/25000) 242 204
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t199 : ((520347718121/10000000000000 : ℚ) : ℝ) ≤ stT242 199 := by
  have hc : ((734041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520347718121/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((734041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c200 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((893123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116639/1000000) (δ := 12137/1000000000) (ψ := -1089/25000) 242 204
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t200 : ((315748638369/5000000000000 : ℚ) : ℝ) ≤ stT242 200 := by
  have hc : ((893073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315748638369/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((893073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c201 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-51289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 261493/625000) (δ := 12137/1000000000) (ψ := -1089/25000) 242 204
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t201 : ((-9048531161/1250000000000 : ℚ) : ℝ) ≤ stT242 201 := by
  have hc : ((-25657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9048531161/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-25657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c202 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-19291/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3593161/5000000) (δ := 6133/500000000) (ψ := -1089/25000) 242 204
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t202 : ((-1696726577/25000000000 : ℚ) : ℝ) ≤ stT242 202 := by
  have hc : ((-4823/5000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1696726577/25000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-4823/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c203 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-74929/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553397/1000000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 205
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t203 : ((-210377117483/5000000000000 : ℚ) : ℝ) ≤ stT242 203 := by
  have hc : ((-299741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210377117483/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-299741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c204 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((129903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2561/10000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 205
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t204 : ((9094153467/250000000000 : ℚ) : ℝ) ≤ stT242 204 := by
  have hc : ((259781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9094153467/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((259781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c205 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((987389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7949/200000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 205
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t205 : ((68958717777/1000000000000 : ℚ) : ℝ) ≤ stT242 205 := by
  have hc : ((987339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68958717777/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((987339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c206 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((232061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3341501/10000000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 205
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t206 : ((161649720063/10000000000000 : ℚ) : ℝ) ≤ stT242 206 := by
  have hc : ((232011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161649720063/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((232011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c207 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-806207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3135637/5000000) (δ := 12173/1000000000) (ψ := -1089/25000) 242 205
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t207 : ((-560388121593/10000000000000 : ℚ) : ℝ) ≤ stT242 207 := by
  have hc : ((-806257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560388121593/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-806257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c208 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-861191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6521013/10000000) (δ := 12123/1000000000) (ψ := -1089/25000) 242 206
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t208 : ((-4665342497/78125000000 : ℚ) : ℝ) ≤ stT242 208 := by
  have hc : ((-861241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4665342497/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-861241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c209 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((122761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226207/625000) (δ := 12123/1000000000) (ψ := -1089/25000) 242 206
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t209 : ((42440458327/5000000000000 : ℚ) : ℝ) ≤ stT242 209 := by
  have hc : ((122711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42440458327/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((122711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c210 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((957501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146293/2000000) (δ := 307/25000000) (ψ := -1089/25000) 242 206
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t210 : ((132140684863/2000000000000 : ℚ) : ℝ) ≤ stT242 210 := by
  have hc : ((957451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132140684863/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((957451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c211 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((654663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267831/1250000) (δ := 307/25000000) (ψ := -1089/25000) 242 206
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t211 : ((112663479591/2500000000000 : ℚ) : ℝ) ≤ stT242 211 := by
  have hc : ((654613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112663479591/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((654613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c212 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-417291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1250787/2500000) (δ := 12123/1000000000) (ψ := -1089/25000) 242 206
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t212 : ((-286631050823/10000000000000 : ℚ) : ℝ) ≤ stT242 212 := by
  have hc : ((-417341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286631050823/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-417341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c213 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3925109/5000000) (δ := 307/25000000) (ψ := -1089/25000) 242 206
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t213 : ((-685222574261/10000000000000 : ℚ) : ℝ) ≤ stT242 213 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685222574261/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c214 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-106213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2511993/5000000) (δ := 3047/250000000) (ψ := -1089/25000) 242 207
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t214 : ((-72614264643/2500000000000 : ℚ) : ℝ) ≤ stT242 214 := by
  have hc : ((-212451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72614264643/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-212451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c215 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((636079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -550869/2500000) (δ := 3047/250000000) (ψ := -1089/25000) 242 207
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t215 : ((216883980913/5000000000000 : ℚ) : ℝ) ≤ stT242 215 := by
  have hc : ((636029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216883980913/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((636029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c216 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((12137/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 301983/5000000) (δ := 3047/250000000) (ψ := -1089/25000) 242 207
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t216 : ((66061978583/1000000000000 : ℚ) : ℝ) ≤ stT242 216 := by
  have hc : ((97091/100000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66061978583/1000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((97091/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c217 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((26233/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1062/3125) (δ := 2443/200000000) (ψ := -1089/25000) 242 207
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t217 : ((17803871877/1250000000000 : ℚ) : ℝ) ≤ stT242 217 := by
  have hc : ((104907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17803871877/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((104907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c218 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-784077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6180009/10000000) (δ := 3047/250000000) (ψ := -1089/25000) 242 207
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t218 : ((-265539119661/5000000000000 : ℚ) : ℝ) ≤ stT242 218 := by
  have hc : ((-784127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265539119661/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-784127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c219 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-452807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6759051/10000000) (δ := 3027/250000000) (ψ := -1089/25000) 242 208
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t219 : ((-4781184219/78125000000 : ℚ) : ℝ) ≤ stT242 219 := by
  have hc : ((-14151/15625 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4781184219/78125000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-14151/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c220 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-7579/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -500349/1250000) (δ := 3027/250000000) (ψ := -1089/25000) 242 208
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t220 : ((-51181893/25000000000 : ℚ) : ℝ) ≤ stT242 220 := by
  have hc : ((-15183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51181893/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-15183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c221 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((218963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314749/2500000) (δ := 3027/250000000) (ψ := -1089/25000) 242 208
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t221 : ((9205116921/156250000000 : ℚ) : ℝ) ≤ stT242 221 := by
  have hc : ((437901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9205116921/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((437901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c222 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((831533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1472337/10000000) (δ := 3027/250000000) (ψ := -1089/25000) 242 208
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t222 : ((139513701087/2500000000000 : ℚ) : ℝ) ≤ stT242 222 := by
  have hc : ((831483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139513701087/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((831483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c223 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-52793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4191449/10000000) (δ := 3027/250000000) (ψ := -1089/25000) 242 208
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t223 : ((-353695737/50000000000 : ℚ) : ℝ) ≤ stT242 223 := by
  have hc : ((-26409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353695737/50000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-26409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c224 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-463917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6898401/10000000) (δ := 2459/200000000) (ψ := -1089/25000) 242 208
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t224 : ((-77496175767/1250000000000 : ℚ) : ℝ) ≤ stT242 224 := by
  have hc : ((-231971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77496175767/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-231971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c225 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-153517/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6114651/10000000) (δ := 12201/1000000000) (ψ := -1089/25000) 242 209
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t225 : ((-102351384509/2000000000000 : ℚ) : ℝ) ≤ stT242 225 := by
  have hc : ((-153527/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102351384509/2000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-153527/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c226 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((49201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857937/2500000) (δ := 12101/500000000) (ψ := -1089/25000) 242 209
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t226 : ((6543939663/500000000000 : ℚ) : ℝ) ≤ stT242 226 := by
  have hc : ((98377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6543939663/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((98377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c227 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((95407/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760643/10000000) (δ := 12201/1000000000) (ψ := -1089/25000) 242 209
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t227 : ((31660250823/500000000000 : ℚ) : ℝ) ≤ stT242 227 := by
  have hc : ((47701/50000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31660250823/500000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((47701/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c228 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((181299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379739/2000000) (δ := 12201/1000000000) (ψ := -1089/25000) 242 209
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t228 : ((120059885209/2500000000000 : ℚ) : ℝ) ≤ stT242 228 := by
  have hc : ((362573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120059885209/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((362573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c229 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-245243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4546417/10000000) (δ := 12201/1000000000) (ψ := -1089/25000) 242 209
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t229 : ((-162094274967/10000000000000 : ℚ) : ℝ) ≤ stT242 229 := by
  have hc : ((-245293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162094274967/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-245293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c230 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-482077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897823/1250000) (δ := 6101/500000000) (ψ := -1089/25000) 242 209
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t230 : ((-158944449431/2500000000000 : ℚ) : ℝ) ≤ stT242 230 := by
  have hc : ((-241051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158944449431/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-241051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c231 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-28399/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -737581/1250000) (δ := 6147/500000000) (ψ := -1089/25000) 242 210
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t231 : ((-583952961/12500000000 : ℚ) : ℝ) ≤ stT242 231 := by
  have hc : ((-28401/40000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583952961/12500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-28401/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c232 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((253097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328729/1000000) (δ := 6147/500000000) (ψ := -1089/25000) 242 210
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t232 : ((41533363251/2500000000000 : ℚ) : ℝ) ≤ stT242 232 := by
  have hc : ((253047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41533363251/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((253047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c233 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((962683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171281/2500000) (δ := 12109/1000000000) (ψ := -1089/25000) 242 210
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t233 : ((630641093593/10000000000000 : ℚ) : ℝ) ≤ stT242 233 := by
  have hc : ((962633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630641093593/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((962633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c234 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((361603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1905909/10000000) (δ := 6147/500000000) (ψ := -1089/25000) 242 210
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t234 : ((2954634627/62500000000 : ℚ) : ℝ) ≤ stT242 234 := by
  have hc : ((180789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2954634627/62500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((180789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c235 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-44339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4485871/10000000) (δ := 6147/500000000) (ψ := -1089/25000) 242 210
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t235 : ((-28930138821/2000000000000 : ℚ) : ℝ) ≤ stT242 235 := by
  have hc : ((-44349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28930138821/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-44349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c236 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-949349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7054883/10000000) (δ := 12109/1000000000) (ψ := -1089/25000) 242 210
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t236 : ((-123601306411/2000000000000 : ℚ) : ℝ) ≤ stT242 236 := by
  have hc : ((-949399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123601306411/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-949399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c237 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-47657/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6094959/10000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 211
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t237 : ((-24766869917/500000000000 : ℚ) : ℝ) ≤ stT242 237 := by
  have hc : ((-381281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24766869917/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-381281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c238 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((37793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1773803/5000000) (δ := 1527/125000000) (ψ := -1089/25000) 242 211
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t238 : ((48978866883/5000000000000 : ℚ) : ℝ) ≤ stT242 238 := by
  have hc : ((75561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48978866883/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((75561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c239 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((459677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -505451/5000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 211
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t239 : ((37165507199/625000000000 : ℚ) : ℝ) ≤ stT242 239 := by
  have hc : ((114913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37165507199/625000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((114913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c240 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((205471/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303043/2000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 211
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t240 : ((265245690749/5000000000000 : ℚ) : ℝ) ≤ stT242 240 := by
  have hc : ((410917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265245690749/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((410917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c241 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-20757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806161/2000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 211
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t241 : ((-6693435387/2500000000000 : ℚ) : ℝ) ≤ stT242 241 := by
  have hc : ((-10391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6693435387/2500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-10391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c242 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-864221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6535989/10000000) (δ := 12187/1000000000) (ψ := -1089/25000) 242 211
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t242 : ((-22223000223/400000000000 : ℚ) : ℝ) ≤ stT242 242 := by
  have hc : ((-864271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22223000223/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-864271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c243 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-445617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417321/625000) (δ := 12279/1000000000) (ψ := -1089/25000) 242 212
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t243 : ((-142939894321/2500000000000 : ℚ) : ℝ) ≤ stT242 243 := by
  have hc : ((-222821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142939894321/2500000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-222821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c244 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-106013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2096261/5000000) (δ := 12279/1000000000) (ψ := -1089/25000) 242 212
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t244 : ((-13579988331/2000000000000 : ℚ) : ℝ) ≤ stT242 244 := by
  have hc : ((-106063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13579988331/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-106063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c245 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((772999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -859051/5000000) (δ := 24279/1000000000) (ψ := -1089/25000) 242 212
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t245 : ((123454641331/2500000000000 : ℚ) : ℝ) ≤ stT242 245 := by
  have hc : ((772949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123454641331/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((772949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c246 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((14934/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29851/400000) (δ := 3031/250000000) (ψ := -1089/25000) 242 212
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t246 : ((38084247511/625000000000 : ℚ) : ℝ) ≤ stT242 246 := by
  have hc : ((477863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38084247511/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((477863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c247 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((28647/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3200639/10000000) (δ := 3031/250000000) (ψ := -1089/25000) 242 212
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t247 : ((2278055791/125000000000 : ℚ) : ℝ) ≤ stT242 247 := by
  have hc : ((14321/50000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2278055791/125000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((14321/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c248 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-634403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5645081/10000000) (δ := 3031/250000000) (ψ := -1089/25000) 242 212
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t248 : ((-402878289453/10000000000000 : ℚ) : ℝ) ≤ stT242 248 := by
  have hc : ((-634453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402878289453/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-634453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c249 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-124491/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3814151/5000000) (δ := 3043/250000000) (ψ := -1089/25000) 242 213
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t249 : ((-12623523161/200000000000 : ℚ) : ℝ) ≤ stT242 249 := by
  have hc : ((-497989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12623523161/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-497989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_c250 :
    |Real.cos (((242 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-488669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5203401/10000000) (δ := 12231/1000000000) (ψ := -1089/25000) 242 213
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st242_t250 : ((-38636657983/1250000000000 : ℚ) : ℝ) ≤ stT242 250 := by
  have hc : ((-488719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((242 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st242_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38636657983/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-488719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st242_p1 : ((999001/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT242 (i+1) := by
  rw [Finset.sum_range_one]
  exact st242_t1

theorem st242_p2 : ((1991855730621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT242 (i+1))
      = (∑ i ∈ Finset.range 1, stT242 (i+1)) + stT242 2 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 1
    simpa using h
  have hprev := st242_p1
  have hstep := st242_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p3 : ((1098310862097/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT242 (i+1))
      = (∑ i ∈ Finset.range 2, stT242 (i+1)) + stT242 3 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 2
    simpa using h
  have hprev := st242_p2
  have hstep := st242_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p4 : ((716229249333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT242 (i+1))
      = (∑ i ∈ Finset.range 3, stT242 (i+1)) + stT242 4 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 3
    simpa using h
  have hprev := st242_p3
  have hstep := st242_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p5 : ((1475591593859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT242 (i+1))
      = (∑ i ∈ Finset.range 4, stT242 (i+1)) + stT242 5 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 4
    simpa using h
  have hprev := st242_p4
  have hstep := st242_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p6 : ((622510355579/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT242 (i+1))
      = (∑ i ∈ Finset.range 5, stT242 (i+1)) + stT242 6 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 5
    simpa using h
  have hprev := st242_p5
  have hstep := st242_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p7 : ((679353524779/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT242 (i+1))
      = (∑ i ∈ Finset.range 6, stT242 (i+1)) + stT242 7 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 6
    simpa using h
  have hprev := st242_p6
  have hstep := st242_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p8 : ((4119374000567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT242 (i+1))
      = (∑ i ∈ Finset.range 7, stT242 (i+1)) + stT242 8 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 7
    simpa using h
  have hprev := st242_p7
  have hstep := st242_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p9 : ((3564817222989/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT242 (i+1))
      = (∑ i ∈ Finset.range 8, stT242 (i+1)) + stT242 9 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 8
    simpa using h
  have hprev := st242_p8
  have hstep := st242_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p10 : ((3283652761453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT242 (i+1))
      = (∑ i ∈ Finset.range 9, stT242 (i+1)) + stT242 10 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 9
    simpa using h
  have hprev := st242_p9
  have hstep := st242_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p11 : ((5584135642229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT242 (i+1))
      = (∑ i ∈ Finset.range 10, stT242 (i+1)) + stT242 11 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 10
    simpa using h
  have hprev := st242_p10
  have hstep := st242_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p12 : ((5263410278149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT242 (i+1))
      = (∑ i ∈ Finset.range 11, stT242 (i+1)) + stT242 12 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 11
    simpa using h
  have hprev := st242_p11
  have hstep := st242_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p13 : ((5668850215399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT242 (i+1))
      = (∑ i ∈ Finset.range 12, stT242 (i+1)) + stT242 13 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 12
    simpa using h
  have hprev := st242_p12
  have hstep := st242_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p14 : ((9787587563411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT242 (i+1))
      = (∑ i ∈ Finset.range 13, stT242 (i+1)) + stT242 14 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 13
    simpa using h
  have hprev := st242_p13
  have hstep := st242_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p15 : ((4427304538081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT242 (i+1))
      = (∑ i ∈ Finset.range 14, stT242 (i+1)) + stT242 15 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 14
    simpa using h
  have hprev := st242_p14
  have hstep := st242_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p16 : ((4772693288081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT242 (i+1))
      = (∑ i ∈ Finset.range 15, stT242 (i+1)) + stT242 16 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 15
    simpa using h
  have hprev := st242_p15
  have hstep := st242_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p17 : ((5605258581659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT242 (i+1))
      = (∑ i ∈ Finset.range 16, stT242 (i+1)) + stT242 17 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 16
    simpa using h
  have hprev := st242_p16
  have hstep := st242_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p18 : ((5030743653501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT242 (i+1))
      = (∑ i ∈ Finset.range 17, stT242 (i+1)) + stT242 18 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 17
    simpa using h
  have hprev := st242_p17
  have hstep := st242_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p19 : ((4049043621247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT242 (i+1))
      = (∑ i ∈ Finset.range 18, stT242 (i+1)) + stT242 19 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 18
    simpa using h
  have hprev := st242_p18
  have hstep := st242_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p20 : ((3191811176359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT242 (i+1))
      = (∑ i ∈ Finset.range 19, stT242 (i+1)) + stT242 20 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 19
    simpa using h
  have hprev := st242_p19
  have hstep := st242_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p21 : ((3067082189077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT242 (i+1))
      = (∑ i ∈ Finset.range 20, stT242 (i+1)) + stT242 21 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 20
    simpa using h
  have hprev := st242_p20
  have hstep := st242_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p22 : ((4058256507391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT242 (i+1))
      = (∑ i ∈ Finset.range 21, stT242 (i+1)) + stT242 22 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 21
    simpa using h
  have hprev := st242_p21
  have hstep := st242_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p23 : ((4202183571991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT242 (i+1))
      = (∑ i ∈ Finset.range 22, stT242 (i+1)) + stT242 23 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 22
    simpa using h
  have hprev := st242_p22
  have hstep := st242_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p24 : ((1668056074079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT242 (i+1))
      = (∑ i ∈ Finset.range 23, stT242 (i+1)) + stT242 24 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 23
    simpa using h
  have hprev := st242_p23
  have hstep := st242_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p25 : ((2165357574079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT242 (i+1))
      = (∑ i ∈ Finset.range 24, stT242 (i+1)) + stT242 25 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 24
    simpa using h
  have hprev := st242_p24
  have hstep := st242_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p26 : ((1675374976513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT242 (i+1))
      = (∑ i ∈ Finset.range 25, stT242 (i+1)) + stT242 26 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 25
    simpa using h
  have hprev := st242_p25
  have hstep := st242_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p27 : ((266344432361/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT242 (i+1))
      = (∑ i ∈ Finset.range 26, stT242 (i+1)) + stT242 27 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 26
    simpa using h
  have hprev := st242_p26
  have hstep := st242_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p28 : ((7427111588029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT242 (i+1))
      = (∑ i ∈ Finset.range 27, stT242 (i+1)) + stT242 28 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 27
    simpa using h
  have hprev := st242_p27
  have hstep := st242_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p29 : ((6853225525191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT242 (i+1))
      = (∑ i ∈ Finset.range 28, stT242 (i+1)) + stT242 29 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 28
    simpa using h
  have hprev := st242_p28
  have hstep := st242_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p30 : ((8677688506491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT242 (i+1))
      = (∑ i ∈ Finset.range 29, stT242 (i+1)) + stT242 30 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 29
    simpa using h
  have hprev := st242_p29
  have hstep := st242_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p31 : ((1693510396909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT242 (i+1))
      = (∑ i ∈ Finset.range 30, stT242 (i+1)) + stT242 31 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 30
    simpa using h
  have hprev := st242_p30
  have hstep := st242_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p32 : ((83777916773/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT242 (i+1))
      = (∑ i ∈ Finset.range 31, stT242 (i+1)) + stT242 32 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 31
    simpa using h
  have hprev := st242_p31
  have hstep := st242_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p33 : ((741004151969/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT242 (i+1))
      = (∑ i ∈ Finset.range 32, stT242 (i+1)) + stT242 33 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 32
    simpa using h
  have hprev := st242_p32
  have hstep := st242_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p34 : ((6720512349387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT242 (i+1))
      = (∑ i ∈ Finset.range 33, stT242 (i+1)) + stT242 34 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 33
    simpa using h
  have hprev := st242_p33
  have hstep := st242_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p35 : ((8303215342107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT242 (i+1))
      = (∑ i ∈ Finset.range 34, stT242 (i+1)) + stT242 35 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 34
    simpa using h
  have hprev := st242_p34
  have hstep := st242_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p36 : ((9944176352389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT242 (i+1))
      = (∑ i ∈ Finset.range 35, stT242 (i+1)) + stT242 36 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 35
    simpa using h
  have hprev := st242_p35
  have hstep := st242_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p37 : ((5684182833539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT242 (i+1))
      = (∑ i ∈ Finset.range 36, stT242 (i+1)) + stT242 37 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 36
    simpa using h
  have hprev := st242_p36
  have hstep := st242_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p38 : ((6307912761041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT242 (i+1))
      = (∑ i ∈ Finset.range 37, stT242 (i+1)) + stT242 38 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 37
    simpa using h
  have hprev := st242_p37
  have hstep := st242_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p39 : ((692211451293/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT242 (i+1))
      = (∑ i ∈ Finset.range 38, stT242 (i+1)) + stT242 39 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 38
    simpa using h
  have hprev := st242_p38
  have hstep := st242_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p40 : ((7600123089279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT242 (i+1))
      = (∑ i ∈ Finset.range 39, stT242 (i+1)) + stT242 40 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 39
    simpa using h
  have hprev := st242_p39
  have hstep := st242_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p41 : ((8359942497993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT242 (i+1))
      = (∑ i ∈ Finset.range 40, stT242 (i+1)) + stT242 41 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 40
    simpa using h
  have hprev := st242_p40
  have hstep := st242_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p42 : ((4556490588909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT242 (i+1))
      = (∑ i ∈ Finset.range 41, stT242 (i+1)) + stT242 42 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 41
    simpa using h
  have hprev := st242_p41
  have hstep := st242_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p43 : ((19279707165831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT242 (i+1))
      = (∑ i ∈ Finset.range 42, stT242 (i+1)) + stT242 43 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 42
    simpa using h
  have hprev := st242_p42
  have hstep := st242_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p44 : ((19344732578779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT242 (i+1))
      = (∑ i ∈ Finset.range 43, stT242 (i+1)) + stT242 44 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 43
    simpa using h
  have hprev := st242_p43
  have hstep := st242_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p45 : ((18273656006779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT242 (i+1))
      = (∑ i ∈ Finset.range 44, stT242 (i+1)) + stT242 45 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 44
    simpa using h
  have hprev := st242_p44
  have hstep := st242_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p46 : ((16827124661079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT242 (i+1))
      = (∑ i ∈ Finset.range 45, stT242 (i+1)) + stT242 46 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 45
    simpa using h
  have hprev := st242_p45
  have hstep := st242_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p47 : ((16400077159229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT242 (i+1))
      = (∑ i ∈ Finset.range 46, stT242 (i+1)) + stT242 47 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 46
    simpa using h
  have hprev := st242_p46
  have hstep := st242_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p48 : ((17522693819729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT242 (i+1))
      = (∑ i ∈ Finset.range 47, stT242 (i+1)) + stT242 48 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 47
    simpa using h
  have hprev := st242_p47
  have hstep := st242_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p49 : ((18690482040821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT242 (i+1))
      = (∑ i ∈ Finset.range 48, stT242 (i+1)) + stT242 49 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 48
    simpa using h
  have hprev := st242_p48
  have hstep := st242_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p50 : ((18091822627197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT242 (i+1))
      = (∑ i ∈ Finset.range 49, stT242 (i+1)) + stT242 50 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 49
    simpa using h
  have hprev := st242_p49
  have hstep := st242_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p51 : ((1677986155071/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT242 (i+1))
      = (∑ i ∈ Finset.range 50, stT242 (i+1)) + stT242 51 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 50
    simpa using h
  have hprev := st242_p50
  have hstep := st242_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p52 : ((864089993673/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT242 (i+1))
      = (∑ i ∈ Finset.range 51, stT242 (i+1)) + stT242 52 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 51
    simpa using h
  have hprev := st242_p51
  have hstep := st242_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p53 : ((231305433689/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT242 (i+1))
      = (∑ i ∈ Finset.range 52, stT242 (i+1)) + stT242 53 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 52
    simpa using h
  have hprev := st242_p52
  have hstep := st242_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p54 : ((2208478447367/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT242 (i+1))
      = (∑ i ∈ Finset.range 53, stT242 (i+1)) + stT242 54 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 53
    simpa using h
  have hprev := st242_p53
  have hstep := st242_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p55 : ((2108239234117/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT242 (i+1))
      = (∑ i ∈ Finset.range 54, stT242 (i+1)) + stT242 55 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 54
    simpa using h
  have hprev := st242_p54
  have hstep := st242_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p56 : ((1814827186341/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT242 (i+1))
      = (∑ i ∈ Finset.range 55, stT242 (i+1)) + stT242 56 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 55
    simpa using h
  have hprev := st242_p55
  have hstep := st242_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p57 : ((17957935146777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT242 (i+1))
      = (∑ i ∈ Finset.range 56, stT242 (i+1)) + stT242 57 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 56
    simpa using h
  have hprev := st242_p56
  have hstep := st242_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p58 : ((16910752678627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT242 (i+1))
      = (∑ i ∈ Finset.range 57, stT242 (i+1)) + stT242 58 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 57
    simpa using h
  have hprev := st242_p57
  have hstep := st242_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p59 : ((1813474575409/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT242 (i+1))
      = (∑ i ∈ Finset.range 58, stT242 (i+1)) + stT242 59 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 58
    simpa using h
  have hprev := st242_p58
  have hstep := st242_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p60 : ((1775620020019/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT242 (i+1))
      = (∑ i ∈ Finset.range 59, stT242 (i+1)) + stT242 60 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 59
    simpa using h
  have hprev := st242_p59
  have hstep := st242_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p61 : ((17074983714847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT242 (i+1))
      = (∑ i ∈ Finset.range 60, stT242 (i+1)) + stT242 61 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 60
    simpa using h
  have hprev := st242_p60
  have hstep := st242_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p62 : ((4578825880369/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT242 (i+1))
      = (∑ i ∈ Finset.range 61, stT242 (i+1)) + stT242 62 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 61
    simpa using h
  have hprev := st242_p61
  have hstep := st242_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p63 : ((8609112366699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT242 (i+1))
      = (∑ i ∈ Finset.range 62, stT242 (i+1)) + stT242 63 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 62
    simpa using h
  have hprev := st242_p62
  have hstep := st242_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p64 : ((8845072366699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT242 (i+1))
      = (∑ i ∈ Finset.range 63, stT242 (i+1)) + stT242 64 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 63
    simpa using h
  have hprev := st242_p63
  have hstep := st242_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p65 : ((17964679417337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT242 (i+1))
      = (∑ i ∈ Finset.range 64, stT242 (i+1)) + stT242 65 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 64
    simpa using h
  have hprev := st242_p64
  have hstep := st242_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p66 : ((4275528625043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT242 (i+1))
      = (∑ i ∈ Finset.range 65, stT242 (i+1)) + stT242 66 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 65
    simpa using h
  have hprev := st242_p65
  have hstep := st242_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p67 : ((4567579462519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT242 (i+1))
      = (∑ i ∈ Finset.range 66, stT242 (i+1)) + stT242 67 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 66
    simpa using h
  have hprev := st242_p66
  have hstep := st242_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p68 : ((17070625429487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT242 (i+1))
      = (∑ i ∈ Finset.range 67, stT242 (i+1)) + stT242 68 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 67
    simpa using h
  have hprev := st242_p67
  have hstep := st242_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p69 : ((18104273558441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT242 (i+1))
      = (∑ i ∈ Finset.range 68, stT242 (i+1)) + stT242 69 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 68
    simpa using h
  have hprev := st242_p68
  have hstep := st242_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p70 : ((17341394744611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT242 (i+1))
      = (∑ i ∈ Finset.range 69, stT242 (i+1)) + stT242 70 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 69
    simpa using h
  have hprev := st242_p69
  have hstep := st242_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p71 : ((3560939011703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT242 (i+1))
      = (∑ i ∈ Finset.range 70, stT242 (i+1)) + stT242 71 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 70
    simpa using h
  have hprev := st242_p70
  have hstep := st242_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p72 : ((17619192555667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT242 (i+1))
      = (∑ i ∈ Finset.range 71, stT242 (i+1)) + stT242 72 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 71
    simpa using h
  have hprev := st242_p71
  have hstep := st242_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p73 : ((17574231178687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT242 (i+1))
      = (∑ i ∈ Finset.range 72, stT242 (i+1)) + stT242 73 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 72
    simpa using h
  have hprev := st242_p72
  have hstep := st242_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p74 : ((3558592067579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT242 (i+1))
      = (∑ i ∈ Finset.range 73, stT242 (i+1)) + stT242 74 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 73
    simpa using h
  have hprev := st242_p73
  have hstep := st242_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p75 : ((17455930828819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT242 (i+1))
      = (∑ i ∈ Finset.range 74, stT242 (i+1)) + stT242 75 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 74
    simpa using h
  have hprev := st242_p74
  have hstep := st242_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p76 : ((17859831904633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT242 (i+1))
      = (∑ i ∈ Finset.range 75, stT242 (i+1)) + stT242 76 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 75
    simpa using h
  have hprev := st242_p75
  have hstep := st242_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p77 : ((3487046816467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT242 (i+1))
      = (∑ i ∈ Finset.range 76, stT242 (i+1)) + stT242 77 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 76
    simpa using h
  have hprev := st242_p76
  have hstep := st242_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p78 : ((17836979549259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT242 (i+1))
      = (∑ i ∈ Finset.range 77, stT242 (i+1)) + stT242 78 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 77
    simpa using h
  have hprev := st242_p77
  have hstep := st242_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p79 : ((17500128202059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT242 (i+1))
      = (∑ i ∈ Finset.range 78, stT242 (i+1)) + stT242 79 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 78
    simpa using h
  have hprev := st242_p78
  have hstep := st242_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p80 : ((17729295898201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT242 (i+1))
      = (∑ i ∈ Finset.range 79, stT242 (i+1)) + stT242 80 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 79
    simpa using h
  have hprev := st242_p79
  have hstep := st242_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p81 : ((17650261390529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT242 (i+1))
      = (∑ i ∈ Finset.range 80, stT242 (i+1)) + stT242 81 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 80
    simpa using h
  have hprev := st242_p80
  have hstep := st242_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p82 : ((17538764125589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT242 (i+1))
      = (∑ i ∈ Finset.range 81, stT242 (i+1)) + stT242 82 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 81
    simpa using h
  have hprev := st242_p81
  have hstep := st242_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p83 : ((3574564756959/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT242 (i+1))
      = (∑ i ∈ Finset.range 82, stT242 (i+1)) + stT242 83 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 82
    simpa using h
  have hprev := st242_p82
  have hstep := st242_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p84 : ((691999712243/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT242 (i+1))
      = (∑ i ∈ Finset.range 83, stT242 (i+1)) + stT242 84 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 83
    simpa using h
  have hprev := st242_p83
  have hstep := st242_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p85 : ((18100572277971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT242 (i+1))
      = (∑ i ∈ Finset.range 84, stT242 (i+1)) + stT242 85 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 84
    simpa using h
  have hprev := st242_p84
  have hstep := st242_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p86 : ((17120047549243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT242 (i+1))
      = (∑ i ∈ Finset.range 85, stT242 (i+1)) + stT242 86 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 85
    simpa using h
  have hprev := st242_p85
  have hstep := st242_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p87 : ((3637638761391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT242 (i+1))
      = (∑ i ∈ Finset.range 86, stT242 (i+1)) + stT242 87 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 86
    simpa using h
  have hprev := st242_p86
  have hstep := st242_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p88 : ((17166766896223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT242 (i+1))
      = (∑ i ∈ Finset.range 87, stT242 (i+1)) + stT242 88 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 87
    simpa using h
  have hprev := st242_p87
  have hstep := st242_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p89 : ((8989573768513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT242 (i+1))
      = (∑ i ∈ Finset.range 88, stT242 (i+1)) + stT242 89 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 88
    simpa using h
  have hprev := st242_p88
  have hstep := st242_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p90 : ((219178450239/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT242 (i+1))
      = (∑ i ∈ Finset.range 89, stT242 (i+1)) + stT242 90 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 89
    simpa using h
  have hprev := st242_p89
  have hstep := st242_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p91 : ((3500160226843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT242 (i+1))
      = (∑ i ∈ Finset.range 90, stT242 (i+1)) + stT242 91 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 90
    simpa using h
  have hprev := st242_p90
  have hstep := st242_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p92 : ((18026590002683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT242 (i+1))
      = (∑ i ∈ Finset.range 91, stT242 (i+1)) + stT242 92 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 91
    simpa using h
  have hprev := st242_p91
  have hstep := st242_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p93 : ((3425000550743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT242 (i+1))
      = (∑ i ∈ Finset.range 92, stT242 (i+1)) + stT242 93 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 92
    simpa using h
  have hprev := st242_p92
  have hstep := st242_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p94 : ((9077842112429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT242 (i+1))
      = (∑ i ∈ Finset.range 93, stT242 (i+1)) + stT242 94 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 93
    simpa using h
  have hprev := st242_p93
  have hstep := st242_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p95 : ((17318982960673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT242 (i+1))
      = (∑ i ∈ Finset.range 94, stT242 (i+1)) + stT242 95 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 94
    simpa using h
  have hprev := st242_p94
  have hstep := st242_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p96 : ((17665057852133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT242 (i+1))
      = (∑ i ∈ Finset.range 95, stT242 (i+1)) + stT242 96 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 95
    simpa using h
  have hprev := st242_p95
  have hstep := st242_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p97 : ((17953206954857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT242 (i+1))
      = (∑ i ∈ Finset.range 96, stT242 (i+1)) + stT242 97 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 96
    simpa using h
  have hprev := st242_p96
  have hstep := st242_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p98 : ((3426611938709/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT242 (i+1))
      = (∑ i ∈ Finset.range 97, stT242 (i+1)) + stT242 98 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 97
    simpa using h
  have hprev := st242_p97
  have hstep := st242_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p99 : ((18136163002357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT242 (i+1))
      = (∑ i ∈ Finset.range 98, stT242 (i+1)) + stT242 99 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 98
    simpa using h
  have hprev := st242_p98
  have hstep := st242_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p100 : ((17418659002357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT242 (i+1))
      = (∑ i ∈ Finset.range 99, stT242 (i+1)) + stT242 100 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 99
    simpa using h
  have hprev := st242_p99
  have hstep := st242_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p101 : ((17484775230859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT242 (i+1))
      = (∑ i ∈ Finset.range 100, stT242 (i+1)) + stT242 101 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 100
    simpa using h
  have hprev := st242_p100
  have hstep := st242_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p102 : ((9057797457059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT242 (i+1))
      = (∑ i ∈ Finset.range 101, stT242 (i+1)) + stT242 102 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 101
    simpa using h
  have hprev := st242_p101
  have hstep := st242_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p103 : ((535471195349/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT242 (i+1))
      = (∑ i ∈ Finset.range 102, stT242 (i+1)) + stT242 103 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 102
    simpa using h
  have hprev := st242_p102
  have hstep := st242_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p104 : ((4470617365777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT242 (i+1))
      = (∑ i ∈ Finset.range 103, stT242 (i+1)) + stT242 104 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 103
    simpa using h
  have hprev := st242_p103
  have hstep := st242_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p105 : ((17842421413771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT242 (i+1))
      = (∑ i ∈ Finset.range 104, stT242 (i+1)) + stT242 105 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 104
    simpa using h
  have hprev := st242_p104
  have hstep := st242_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p106 : ((17141063563459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT242 (i+1))
      = (∑ i ∈ Finset.range 105, stT242 (i+1)) + stT242 106 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 105
    simpa using h
  have hprev := st242_p105
  have hstep := st242_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p107 : ((18102405176579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT242 (i+1))
      = (∑ i ∈ Finset.range 106, stT242 (i+1)) + stT242 107 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 106
    simpa using h
  have hprev := st242_p106
  have hstep := st242_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p108 : ((17578913689551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT242 (i+1))
      = (∑ i ∈ Finset.range 107, stT242 (i+1)) + stT242 108 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 107
    simpa using h
  have hprev := st242_p107
  have hstep := st242_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p109 : ((3452610599083/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT242 (i+1))
      = (∑ i ∈ Finset.range 108, stT242 (i+1)) + stT242 109 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 108
    simpa using h
  have hprev := st242_p108
  have hstep := st242_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p110 : ((18172957990869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT242 (i+1))
      = (∑ i ∈ Finset.range 109, stT242 (i+1)) + stT242 110 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 109
    simpa using h
  have hprev := st242_p109
  have hstep := st242_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p111 : ((17416298724849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT242 (i+1))
      = (∑ i ∈ Finset.range 110, stT242 (i+1)) + stT242 111 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 110
    simpa using h
  have hprev := st242_p110
  have hstep := st242_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p112 : ((17370301353601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT242 (i+1))
      = (∑ i ∈ Finset.range 111, stT242 (i+1)) + stT242 112 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 111
    simpa using h
  have hprev := st242_p111
  have hstep := st242_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p113 : ((18181107921601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT242 (i+1))
      = (∑ i ∈ Finset.range 112, stT242 (i+1)) + stT242 113 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 112
    simpa using h
  have hprev := st242_p112
  have hstep := st242_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p114 : ((17349336197447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT242 (i+1))
      = (∑ i ∈ Finset.range 113, stT242 (i+1)) + stT242 114 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 113
    simpa using h
  have hprev := st242_p113
  have hstep := st242_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p115 : ((17409883682167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT242 (i+1))
      = (∑ i ∈ Finset.range 114, stT242 (i+1)) + stT242 115 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 114
    simpa using h
  have hprev := st242_p114
  have hstep := st242_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p116 : ((3636324358331/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT242 (i+1))
      = (∑ i ∈ Finset.range 115, stT242 (i+1)) + stT242 116 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 115
    simpa using h
  have hprev := st242_p115
  have hstep := st242_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p117 : ((17359359508243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT242 (i+1))
      = (∑ i ∈ Finset.range 116, stT242 (i+1)) + stT242 117 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 116
    simpa using h
  have hprev := st242_p116
  have hstep := st242_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p118 : ((17372150883973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT242 (i+1))
      = (∑ i ∈ Finset.range 117, stT242 (i+1)) + stT242 118 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 117
    simpa using h
  have hprev := st242_p117
  have hstep := st242_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p119 : ((18182940013939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT242 (i+1))
      = (∑ i ∈ Finset.range 118, stT242 (i+1)) + stT242 119 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 118
    simpa using h
  have hprev := st242_p118
  have hstep := st242_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p120 : ((3489175037669/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT242 (i+1))
      = (∑ i ∈ Finset.range 119, stT242 (i+1)) + stT242 120 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 119
    simpa using h
  have hprev := st242_p119
  have hstep := st242_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p121 : ((863545803997/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT242 (i+1))
      = (∑ i ∈ Finset.range 120, stT242 (i+1)) + stT242 121 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 120
    simpa using h
  have hprev := st242_p120
  have hstep := st242_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p122 : ((2269115716703/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT242 (i+1))
      = (∑ i ∈ Finset.range 121, stT242 (i+1)) + stT242 122 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 121
    simpa using h
  have hprev := st242_p121
  have hstep := st242_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p123 : ((4405035388501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT242 (i+1))
      = (∑ i ∈ Finset.range 122, stT242 (i+1)) + stT242 123 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 122
    simpa using h
  have hprev := st242_p122
  have hstep := st242_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p124 : ((535960264771/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT242 (i+1))
      = (∑ i ∈ Finset.range 123, stT242 (i+1)) + stT242 124 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 123
    simpa using h
  have hprev := st242_p123
  have hstep := st242_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p125 : ((9015569900791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT242 (i+1))
      = (∑ i ∈ Finset.range 124, stT242 (i+1)) + stT242 125 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 124
    simpa using h
  have hprev := st242_p124
  have hstep := st242_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p126 : ((17871140260853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT242 (i+1))
      = (∑ i ∈ Finset.range 125, stT242 (i+1)) + stT242 126 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 125
    simpa using h
  have hprev := st242_p125
  have hstep := st242_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p127 : ((8551126703283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT242 (i+1))
      = (∑ i ∈ Finset.range 126, stT242 (i+1)) + stT242 127 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 126
    simpa using h
  have hprev := st242_p126
  have hstep := st242_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p128 : ((277597921481/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT242 (i+1))
      = (∑ i ∈ Finset.range 127, stT242 (i+1)) + stT242 128 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 127
    simpa using h
  have hprev := st242_p127
  have hstep := st242_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p129 : ((4528946563721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT242 (i+1))
      = (∑ i ∈ Finset.range 128, stT242 (i+1)) + stT242 129 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 128
    simpa using h
  have hprev := st242_p128
  have hstep := st242_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p130 : ((4311004418693/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT242 (i+1))
      = (∑ i ∈ Finset.range 129, stT242 (i+1)) + stT242 130 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 129
    simpa using h
  have hprev := st242_p129
  have hstep := st242_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p131 : ((4348652542479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT242 (i+1))
      = (∑ i ∈ Finset.range 130, stT242 (i+1)) + stT242 131 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 130
    simpa using h
  have hprev := st242_p130
  have hstep := st242_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p132 : ((909050634551/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT242 (i+1))
      = (∑ i ∈ Finset.range 131, stT242 (i+1)) + stT242 132 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 131
    simpa using h
  have hprev := st242_p131
  have hstep := st242_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p133 : ((110146316679/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT242 (i+1))
      = (∑ i ∈ Finset.range 132, stT242 (i+1)) + stT242 133 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 132
    simpa using h
  have hprev := st242_p132
  have hstep := st242_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p134 : ((8557060077583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT242 (i+1))
      = (∑ i ∈ Finset.range 133, stT242 (i+1)) + stT242 134 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 133
    simpa using h
  have hprev := st242_p133
  have hstep := st242_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p135 : ((4476534153677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT242 (i+1))
      = (∑ i ∈ Finset.range 134, stT242 (i+1)) + stT242 135 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 134
    simpa using h
  have hprev := st242_p134
  have hstep := st242_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p136 : ((9032665431/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT242 (i+1))
      = (∑ i ∈ Finset.range 135, stT242 (i+1)) + stT242 136 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 135
    simpa using h
  have hprev := st242_p135
  have hstep := st242_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p137 : ((2151378869793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT242 (i+1))
      = (∑ i ∈ Finset.range 136, stT242 (i+1)) + stT242 137 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 136
    simpa using h
  have hprev := st242_p136
  have hstep := st242_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p138 : ((2172985662399/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT242 (i+1))
      = (∑ i ∈ Finset.range 137, stT242 (i+1)) + stT242 138 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 137
    simpa using h
  have hprev := st242_p137
  have hstep := st242_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p139 : ((227139943171/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT242 (i+1))
      = (∑ i ∈ Finset.range 138, stT242 (i+1)) + stT242 139 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 138
    simpa using h
  have hprev := st242_p138
  have hstep := st242_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p140 : ((886649467371/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT242 (i+1))
      = (∑ i ∈ Finset.range 139, stT242 (i+1)) + stT242 140 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 139
    simpa using h
  have hprev := st242_p139
  have hstep := st242_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p141 : ((4271753953417/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT242 (i+1))
      = (∑ i ∈ Finset.range 140, stT242 (i+1)) + stT242 141 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 140
    simpa using h
  have hprev := st242_p140
  have hstep := st242_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p142 : ((8854839861929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT242 (i+1))
      = (∑ i ∈ Finset.range 141, stT242 (i+1)) + stT242 142 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 141
    simpa using h
  have hprev := st242_p141
  have hstep := st242_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p143 : ((909339503539/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT242 (i+1))
      = (∑ i ∈ Finset.range 142, stT242 (i+1)) + stT242 143 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 142
    simpa using h
  have hprev := st242_p142
  have hstep := st242_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p144 : ((8726053491517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT242 (i+1))
      = (∑ i ∈ Finset.range 143, stT242 (i+1)) + stT242 144 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 143
    simpa using h
  have hprev := st242_p143
  have hstep := st242_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p145 : ((17138137691639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT242 (i+1))
      = (∑ i ∈ Finset.range 144, stT242 (i+1)) + stT242 145 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 144
    simpa using h
  have hprev := st242_p144
  have hstep := st242_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p146 : ((8964949973347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT242 (i+1))
      = (∑ i ∈ Finset.range 145, stT242 (i+1)) + stT242 146 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 145
    simpa using h
  have hprev := st242_p145
  have hstep := st242_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p147 : ((1810513068111/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT242 (i+1))
      = (∑ i ∈ Finset.range 146, stT242 (i+1)) + stT242 147 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 146
    simpa using h
  have hprev := st242_p146
  have hstep := st242_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p148 : ((1729163182143/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT242 (i+1))
      = (∑ i ∈ Finset.range 147, stT242 (i+1)) + stT242 148 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 147
    simpa using h
  have hprev := st242_p147
  have hstep := st242_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p149 : ((8610860100507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT242 (i+1))
      = (∑ i ∈ Finset.range 148, stT242 (i+1)) + stT242 149 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 148
    simpa using h
  have hprev := st242_p148
  have hstep := st242_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p150 : ((9018801098011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT242 (i+1))
      = (∑ i ∈ Finset.range 149, stT242 (i+1)) + stT242 150 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 149
    simpa using h
  have hprev := st242_p149
  have hstep := st242_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p151 : ((9018893462949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT242 (i+1))
      = (∑ i ∈ Finset.range 150, stT242 (i+1)) + stT242 151 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 150
    simpa using h
  have hprev := st242_p150
  have hstep := st242_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p152 : ((8613459506933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT242 (i+1))
      = (∑ i ∈ Finset.range 151, stT242 (i+1)) + stT242 152 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 151
    simpa using h
  have hprev := st242_p151
  have hstep := st242_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p153 : ((8630569585061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT242 (i+1))
      = (∑ i ∈ Finset.range 152, stT242 (i+1)) + stT242 153 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 152
    simpa using h
  have hprev := st242_p152
  have hstep := st242_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p154 : ((4516496732831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT242 (i+1))
      = (∑ i ∈ Finset.range 153, stT242 (i+1)) + stT242 154 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 153
    simpa using h
  have hprev := st242_p153
  have hstep := st242_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p155 : ((2253857062273/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT242 (i+1))
      = (∑ i ∈ Finset.range 154, stT242 (i+1)) + stT242 155 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 154
    simpa using h
  have hprev := st242_p154
  have hstep := st242_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p156 : ((10769072837/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT242 (i+1))
      = (∑ i ∈ Finset.range 155, stT242 (i+1)) + stT242 156 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 155
    simpa using h
  have hprev := st242_p155
  have hstep := st242_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p157 : ((8617120603281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT242 (i+1))
      = (∑ i ∈ Finset.range 156, stT242 (i+1)) + stT242 157 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 156
    simpa using h
  have hprev := st242_p156
  have hstep := st242_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p158 : ((18029410770303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT242 (i+1))
      = (∑ i ∈ Finset.range 157, stT242 (i+1)) + stT242 158 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 157
    simpa using h
  have hprev := st242_p157
  have hstep := st242_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p159 : ((18087641333029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT242 (i+1))
      = (∑ i ∈ Finset.range 158, stT242 (i+1)) + stT242 159 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 158
    simpa using h
  have hprev := st242_p158
  have hstep := st242_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p160 : ((17303408542149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT242 (i+1))
      = (∑ i ∈ Finset.range 159, stT242 (i+1)) + stT242 160 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 159
    simpa using h
  have hprev := st242_p159
  have hstep := st242_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p161 : ((17154441377151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT242 (i+1))
      = (∑ i ∈ Finset.range 160, stT242 (i+1)) + stT242 161 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 160
    simpa using h
  have hprev := st242_p160
  have hstep := st242_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p162 : ((17913173830017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT242 (i+1))
      = (∑ i ∈ Finset.range 161, stT242 (i+1)) + stT242 162 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 161
    simpa using h
  have hprev := st242_p161
  have hstep := st242_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p163 : ((18177290668537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT242 (i+1))
      = (∑ i ∈ Finset.range 162, stT242 (i+1)) + stT242 163 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 162
    simpa using h
  have hprev := st242_p162
  have hstep := st242_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p164 : ((3493799439027/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT242 (i+1))
      = (∑ i ∈ Finset.range 163, stT242 (i+1)) + stT242 164 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 163
    simpa using h
  have hprev := st242_p163
  have hstep := st242_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p165 : ((17072482742467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT242 (i+1))
      = (∑ i ∈ Finset.range 164, stT242 (i+1)) + stT242 165 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 164
    simpa using h
  have hprev := st242_p164
  have hstep := st242_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p166 : ((17693639468217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT242 (i+1))
      = (∑ i ∈ Finset.range 165, stT242 (i+1)) + stT242 166 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 165
    simpa using h
  have hprev := st242_p165
  have hstep := st242_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p167 : ((18226832920491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT242 (i+1))
      = (∑ i ∈ Finset.range 166, stT242 (i+1)) + stT242 167 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 166
    simpa using h
  have hprev := st242_p166
  have hstep := st242_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p168 : ((17738954887337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT242 (i+1))
      = (∑ i ∈ Finset.range 167, stT242 (i+1)) + stT242 168 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 167
    simpa using h
  have hprev := st242_p167
  have hstep := st242_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p169 : ((17083111613661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT242 (i+1))
      = (∑ i ∈ Finset.range 168, stT242 (i+1)) + stT242 169 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 168
    simpa using h
  have hprev := st242_p168
  have hstep := st242_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p170 : ((17386603103281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT242 (i+1))
      = (∑ i ∈ Finset.range 169, stT242 (i+1)) + stT242 170 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 169
    simpa using h
  have hprev := st242_p169
  have hstep := st242_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p171 : ((18126468735781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT242 (i+1))
      = (∑ i ∈ Finset.range 170, stT242 (i+1)) + stT242 171 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 170
    simpa using h
  have hprev := st242_p170
  have hstep := st242_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p172 : ((18053548480219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT242 (i+1))
      = (∑ i ∈ Finset.range 171, stT242 (i+1)) + stT242 172 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 171
    simpa using h
  have hprev := st242_p171
  have hstep := st242_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p173 : ((17295203490377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT242 (i+1))
      = (∑ i ∈ Finset.range 172, stT242 (i+1)) + stT242 173 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 172
    simpa using h
  have hprev := st242_p172
  have hstep := st242_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p174 : ((17108968890037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT242 (i+1))
      = (∑ i ∈ Finset.range 173, stT242 (i+1)) + stT242 174 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 173
    simpa using h
  have hprev := st242_p173
  have hstep := st242_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p175 : ((3559074989561/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT242 (i+1))
      = (∑ i ∈ Finset.range 174, stT242 (i+1)) + stT242 175 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 174
    simpa using h
  have hprev := st242_p174
  have hstep := st242_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p176 : ((18235756930079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT242 (i+1))
      = (∑ i ∈ Finset.range 175, stT242 (i+1)) + stT242 176 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 175
    simpa using h
  have hprev := st242_p175
  have hstep := st242_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p177 : ((17724949655231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT242 (i+1))
      = (∑ i ∈ Finset.range 176, stT242 (i+1)) + stT242 177 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 176
    simpa using h
  have hprev := st242_p176
  have hstep := st242_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p178 : ((683276806247/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT242 (i+1))
      = (∑ i ∈ Finset.range 177, stT242 (i+1)) + stT242 178 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 177
    simpa using h
  have hprev := st242_p177
  have hstep := st242_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p179 : ((216503903839/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT242 (i+1))
      = (∑ i ∈ Finset.range 178, stT242 (i+1)) + stT242 179 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 178
    simpa using h
  have hprev := st242_p178
  have hstep := st242_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p180 : ((3612350391461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT242 (i+1))
      = (∑ i ∈ Finset.range 179, stT242 (i+1)) + stT242 180 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 179
    simpa using h
  have hprev := st242_p179
  have hstep := st242_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p181 : ((18156605191233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT242 (i+1))
      = (∑ i ∈ Finset.range 180, stT242 (i+1)) + stT242 181 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 180
    simpa using h
  have hprev := st242_p180
  have hstep := st242_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p182 : ((17464276949983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT242 (i+1))
      = (∑ i ∈ Finset.range 181, stT242 (i+1)) + stT242 182 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 181
    simpa using h
  have hprev := st242_p181
  have hstep := st242_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p183 : ((17040616994231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT242 (i+1))
      = (∑ i ∈ Finset.range 182, stT242 (i+1)) + stT242 183 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 182
    simpa using h
  have hprev := st242_p182
  have hstep := st242_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p184 : ((17520312992859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT242 (i+1))
      = (∑ i ∈ Finset.range 183, stT242 (i+1)) + stT242 184 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 183
    simpa using h
  have hprev := st242_p183
  have hstep := st242_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p185 : ((18182479805889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT242 (i+1))
      = (∑ i ∈ Finset.range 184, stT242 (i+1)) + stT242 185 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 184
    simpa using h
  have hprev := st242_p184
  have hstep := st242_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p186 : ((18048860009901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT242 (i+1))
      = (∑ i ∈ Finset.range 185, stT242 (i+1)) + stT242 186 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 185
    simpa using h
  have hprev := st242_p185
  have hstep := st242_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p187 : ((17320509176809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT242 (i+1))
      = (∑ i ∈ Finset.range 186, stT242 (i+1)) + stT242 187 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 186
    simpa using h
  have hprev := st242_p186
  have hstep := st242_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p188 : ((2132081656123/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT242 (i+1))
      = (∑ i ∈ Finset.range 187, stT242 (i+1)) + stT242 188 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 187
    simpa using h
  have hprev := st242_p187
  have hstep := st242_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p189 : ((2204068460023/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT242 (i+1))
      = (∑ i ∈ Finset.range 188, stT242 (i+1)) + stT242 189 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 188
    simpa using h
  have hprev := st242_p188
  have hstep := st242_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p190 : ((4555745713017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT242 (i+1))
      = (∑ i ∈ Finset.range 189, stT242 (i+1)) + stT242 190 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 189
    simpa using h
  have hprev := st242_p189
  have hstep := st242_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p191 : ((2249459151621/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT242 (i+1))
      = (∑ i ∈ Finset.range 190, stT242 (i+1)) + stT242 191 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 190
    simpa using h
  have hprev := st242_p190
  have hstep := st242_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p192 : ((1079625293659/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT242 (i+1))
      = (∑ i ∈ Finset.range 191, stT242 (i+1)) + stT242 192 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 191
    simpa using h
  have hprev := st242_p191
  have hstep := st242_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p193 : ((85301964111/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT242 (i+1))
      = (∑ i ∈ Finset.range 192, stT242 (i+1)) + stT242 193 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 192
    simpa using h
  have hprev := st242_p192
  have hstep := st242_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p194 : ((8822054594617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT242 (i+1))
      = (∑ i ∈ Finset.range 193, stT242 (i+1)) + stT242 194 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 193
    simpa using h
  have hprev := st242_p193
  have hstep := st242_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p195 : ((455643048541/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT242 (i+1))
      = (∑ i ∈ Finset.range 194, stT242 (i+1)) + stT242 195 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 194
    simpa using h
  have hprev := st242_p194
  have hstep := st242_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p196 : ((4505377250703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT242 (i+1))
      = (∑ i ∈ Finset.range 195, stT242 (i+1)) + stT242 196 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 195
    simpa using h
  have hprev := st242_p195
  have hstep := st242_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p197 : ((17309869456469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT242 (i+1))
      = (∑ i ∈ Finset.range 196, stT242 (i+1)) + stT242 197 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 196
    simpa using h
  have hprev := st242_p196
  have hstep := st242_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p198 : ((17036480392829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT242 (i+1))
      = (∑ i ∈ Finset.range 197, stT242 (i+1)) + stT242 198 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 197
    simpa using h
  have hprev := st242_p197
  have hstep := st242_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p199 : ((351136562219/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT242 (i+1))
      = (∑ i ∈ Finset.range 198, stT242 (i+1)) + stT242 199 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 198
    simpa using h
  have hprev := st242_p198
  have hstep := st242_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p200 : ((2273540673461/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT242 (i+1))
      = (∑ i ∈ Finset.range 199, stT242 (i+1)) + stT242 200 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 199
    simpa using h
  have hprev := st242_p199
  have hstep := st242_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p201 : ((22644921423/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT242 (i+1))
      = (∑ i ∈ Finset.range 200, stT242 (i+1)) + stT242 201 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 200
    simpa using h
  have hprev := st242_p200
  have hstep := st242_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p202 : ((43593116269/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT242 (i+1))
      = (∑ i ∈ Finset.range 201, stT242 (i+1)) + stT242 202 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 201
    simpa using h
  have hprev := st242_p201
  have hstep := st242_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p203 : ((8508246136317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT242 (i+1))
      = (∑ i ∈ Finset.range 202, stT242 (i+1)) + stT242 203 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 202
    simpa using h
  have hprev := st242_p202
  have hstep := st242_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p204 : ((8690129205657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT242 (i+1))
      = (∑ i ∈ Finset.range 203, stT242 (i+1)) + stT242 204 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 203
    simpa using h
  have hprev := st242_p203
  have hstep := st242_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p205 : ((4517461397271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT242 (i+1))
      = (∑ i ∈ Finset.range 204, stT242 (i+1)) + stT242 205 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 204
    simpa using h
  have hprev := st242_p204
  have hstep := st242_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p206 : ((18231495309147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT242 (i+1))
      = (∑ i ∈ Finset.range 205, stT242 (i+1)) + stT242 206 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 205
    simpa using h
  have hprev := st242_p205
  have hstep := st242_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p207 : ((8835553593777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT242 (i+1))
      = (∑ i ∈ Finset.range 206, stT242 (i+1)) + stT242 207 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 206
    simpa using h
  have hprev := st242_p206
  have hstep := st242_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p208 : ((8536971673969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT242 (i+1))
      = (∑ i ∈ Finset.range 207, stT242 (i+1)) + stT242 208 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 207
    simpa using h
  have hprev := st242_p207
  have hstep := st242_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p209 : ((1072426516537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT242 (i+1))
      = (∑ i ∈ Finset.range 208, stT242 (i+1)) + stT242 209 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 208
    simpa using h
  have hprev := st242_p208
  have hstep := st242_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p210 : ((17819527688907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT242 (i+1))
      = (∑ i ∈ Finset.range 209, stT242 (i+1)) + stT242 210 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 209
    simpa using h
  have hprev := st242_p209
  have hstep := st242_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p211 : ((18270181607271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT242 (i+1))
      = (∑ i ∈ Finset.range 210, stT242 (i+1)) + stT242 211 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 210
    simpa using h
  have hprev := st242_p210
  have hstep := st242_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p212 : ((561985954889/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT242 (i+1))
      = (∑ i ∈ Finset.range 211, stT242 (i+1)) + stT242 212 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 211
    simpa using h
  have hprev := st242_p211
  have hstep := st242_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p213 : ((17298327982187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT242 (i+1))
      = (∑ i ∈ Finset.range 212, stT242 (i+1)) + stT242 213 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 212
    simpa using h
  have hprev := st242_p212
  have hstep := st242_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p214 : ((3401574184723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT242 (i+1))
      = (∑ i ∈ Finset.range 213, stT242 (i+1)) + stT242 214 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 213
    simpa using h
  have hprev := st242_p213
  have hstep := st242_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p215 : ((17441638885441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT242 (i+1))
      = (∑ i ∈ Finset.range 214, stT242 (i+1)) + stT242 215 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 214
    simpa using h
  have hprev := st242_p214
  have hstep := st242_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p216 : ((18102258671271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT242 (i+1))
      = (∑ i ∈ Finset.range 215, stT242 (i+1)) + stT242 216 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 215
    simpa using h
  have hprev := st242_p215
  have hstep := st242_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p217 : ((18244689646287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT242 (i+1))
      = (∑ i ∈ Finset.range 216, stT242 (i+1)) + stT242 217 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 216
    simpa using h
  have hprev := st242_p216
  have hstep := st242_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p218 : ((3542722281393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT242 (i+1))
      = (∑ i ∈ Finset.range 217, stT242 (i+1)) + stT242 218 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 217
    simpa using h
  have hprev := st242_p217
  have hstep := st242_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p219 : ((17101619826933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT242 (i+1))
      = (∑ i ∈ Finset.range 218, stT242 (i+1)) + stT242 219 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 218
    simpa using h
  have hprev := st242_p218
  have hstep := st242_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p220 : ((17081147069733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT242 (i+1))
      = (∑ i ∈ Finset.range 219, stT242 (i+1)) + stT242 220 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 219
    simpa using h
  have hprev := st242_p219
  have hstep := st242_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p221 : ((17670274552677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT242 (i+1))
      = (∑ i ∈ Finset.range 220, stT242 (i+1)) + stT242 221 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 220
    simpa using h
  have hprev := st242_p220
  have hstep := st242_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p222 : ((729133174281/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT242 (i+1))
      = (∑ i ∈ Finset.range 221, stT242 (i+1)) + stT242 222 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 221
    simpa using h
  have hprev := st242_p221
  have hstep := st242_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p223 : ((145260721677/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT242 (i+1))
      = (∑ i ∈ Finset.range 222, stT242 (i+1)) + stT242 223 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 222
    simpa using h
  have hprev := st242_p222
  have hstep := st242_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p224 : ((17537620803489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT242 (i+1))
      = (∑ i ∈ Finset.range 223, stT242 (i+1)) + stT242 224 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 223
    simpa using h
  have hprev := st242_p223
  have hstep := st242_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p225 : ((1064116492559/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT242 (i+1))
      = (∑ i ∈ Finset.range 224, stT242 (i+1)) + stT242 225 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 224
    simpa using h
  have hprev := st242_p224
  have hstep := st242_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p226 : ((4289185668551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT242 (i+1))
      = (∑ i ∈ Finset.range 225, stT242 (i+1)) + stT242 226 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 225
    simpa using h
  have hprev := st242_p225
  have hstep := st242_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p227 : ((2223743461333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT242 (i+1))
      = (∑ i ∈ Finset.range 226, stT242 (i+1)) + stT242 227 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 226
    simpa using h
  have hprev := st242_p226
  have hstep := st242_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p228 : ((36540374463/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT242 (i+1))
      = (∑ i ∈ Finset.range 227, stT242 (i+1)) + stT242 228 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 227
    simpa using h
  have hprev := st242_p227
  have hstep := st242_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p229 : ((18108092956533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT242 (i+1))
      = (∑ i ∈ Finset.range 228, stT242 (i+1)) + stT242 229 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 228
    simpa using h
  have hprev := st242_p228
  have hstep := st242_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p230 : ((17472315158809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT242 (i+1))
      = (∑ i ∈ Finset.range 229, stT242 (i+1)) + stT242 230 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 229
    simpa using h
  have hprev := st242_p229
  have hstep := st242_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p231 : ((17005152790009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT242 (i+1))
      = (∑ i ∈ Finset.range 230, stT242 (i+1)) + stT242 231 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 230
    simpa using h
  have hprev := st242_p230
  have hstep := st242_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p232 : ((17171286243013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT242 (i+1))
      = (∑ i ∈ Finset.range 231, stT242 (i+1)) + stT242 232 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 231
    simpa using h
  have hprev := st242_p231
  have hstep := st242_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p233 : ((8900963668303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT242 (i+1))
      = (∑ i ∈ Finset.range 232, stT242 (i+1)) + stT242 233 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 232
    simpa using h
  have hprev := st242_p232
  have hstep := st242_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p234 : ((9137334438463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT242 (i+1))
      = (∑ i ∈ Finset.range 233, stT242 (i+1)) + stT242 234 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 233
    simpa using h
  have hprev := st242_p233
  have hstep := st242_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p235 : ((18130018182821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT242 (i+1))
      = (∑ i ∈ Finset.range 234, stT242 (i+1)) + stT242 235 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 234
    simpa using h
  have hprev := st242_p234
  have hstep := st242_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p236 : ((8756005825383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT242 (i+1))
      = (∑ i ∈ Finset.range 235, stT242 (i+1)) + stT242 236 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 235
    simpa using h
  have hprev := st242_p235
  have hstep := st242_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p237 : ((8508337126213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT242 (i+1))
      = (∑ i ∈ Finset.range 236, stT242 (i+1)) + stT242 237 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 236
    simpa using h
  have hprev := st242_p236
  have hstep := st242_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p238 : ((1069664499137/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT242 (i+1))
      = (∑ i ∈ Finset.range 237, stT242 (i+1)) + stT242 238 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 237
    simpa using h
  have hprev := st242_p237
  have hstep := st242_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p239 : ((17294218849/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT242 (i+1))
      = (∑ i ∈ Finset.range 238, stT242 (i+1)) + stT242 239 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 238
    simpa using h
  have hprev := st242_p238
  have hstep := st242_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p240 : ((9119885741437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT242 (i+1))
      = (∑ i ∈ Finset.range 239, stT242 (i+1)) + stT242 240 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 239
    simpa using h
  have hprev := st242_p239
  have hstep := st242_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p241 : ((9106498870663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT242 (i+1))
      = (∑ i ∈ Finset.range 240, stT242 (i+1)) + stT242 241 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 240
    simpa using h
  have hprev := st242_p240
  have hstep := st242_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p242 : ((17657422735751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT242 (i+1))
      = (∑ i ∈ Finset.range 241, stT242 (i+1)) + stT242 242 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 241
    simpa using h
  have hprev := st242_p241
  have hstep := st242_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p243 : ((17085663158467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT242 (i+1))
      = (∑ i ∈ Finset.range 242, stT242 (i+1)) + stT242 243 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 242
    simpa using h
  have hprev := st242_p242
  have hstep := st242_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p244 : ((4254440804203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT242 (i+1))
      = (∑ i ∈ Finset.range 243, stT242 (i+1)) + stT242 244 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 243
    simpa using h
  have hprev := st242_p243
  have hstep := st242_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p245 : ((2188947722767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT242 (i+1))
      = (∑ i ∈ Finset.range 244, stT242 (i+1)) + stT242 245 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 244
    simpa using h
  have hprev := st242_p244
  have hstep := st242_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p246 : ((2265116217789/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT242 (i+1))
      = (∑ i ∈ Finset.range 245, stT242 (i+1)) + stT242 246 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 245
    simpa using h
  have hprev := st242_p245
  have hstep := st242_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p247 : ((2287896775699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT242 (i+1))
      = (∑ i ∈ Finset.range 246, stT242 (i+1)) + stT242 247 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 246
    simpa using h
  have hprev := st242_p246
  have hstep := st242_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p248 : ((17900295916139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT242 (i+1))
      = (∑ i ∈ Finset.range 247, stT242 (i+1)) + stT242 248 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 247
    simpa using h
  have hprev := st242_p247
  have hstep := st242_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p249 : ((17269119758089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT242 (i+1))
      = (∑ i ∈ Finset.range 248, stT242 (i+1)) + stT242 249 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 248
    simpa using h
  have hprev := st242_p248
  have hstep := st242_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_p250 : ((678401059769/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT242 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT242 (i+1))
      = (∑ i ∈ Finset.range 249, stT242 (i+1)) + stT242 250 := by
    have h := Finset.sum_range_succ (fun i => stT242 (i+1)) 249
    simpa using h
  have hprev := st242_p249
  have hstep := st242_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st242_s250 :
    |Real.sin (((242 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))
      - ((-872469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -5203401/10000000) (δ := 12231/1000000000) (ψ := -1089/25000) 242 213
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 242`** (evaluated boundary). -/
theorem station_242_sign : 0 < hardyG ((((242:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 242 250 (by norm_num) (by norm_num)
    ((-1089/25000 : ℚ) : ℝ)
  have hchain := st242_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT242 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((242 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-1089/25000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st242_c250
  have hsinb := abs_le.mp st242_s250
  have hbdy_lo : ((10694546268553/187405600000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((242 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1089/25000 : ℚ) : ℝ))) / 2
          - ((((242:ℕ)):ℝ))
            * Real.sin (((242 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-1089/25000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((242:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((242:ℝ) * Real.log (250:ℝ) - ((-1089/25000 : ℚ) : ℝ))) / 2
        - ((242:ℝ)) * Real.sin ((242:ℝ) * Real.log (250:ℝ) - ((-1089/25000 : ℚ) : ℝ))
        ≥ ((84547883/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((242:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((84547883/400000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((84547883/400000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((84547883/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((242:ℕ)):ℝ))+1) * (((((242:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((201423242911/156250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((678401059769/400000000000 : ℚ) : ℝ) + ((10694546268553/187405600000000 : ℚ) : ℝ)
      - ((201423242911/156250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-1089/25000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((242:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-1089/25000 : ℚ) : ℝ)
        * (riemannZeta (line ((((242:ℕ)):ℝ)))).re
      - Real.sin ((-1089/25000 : ℚ) : ℝ)
        * (riemannZeta (line ((((242:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((242:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((242:ℕ)):ℝ))
      = (((((242:ℕ)):ℝ)) * (Real.log ((((242:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((242:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_242
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
  have hθwin : |(((-1089/25000 : ℚ) : ℝ) + ((51:ℤ)) * (2*Real.pi)) - theta ((((242:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((242:ℕ)):ℝ)))
    (φ := ((-1089/25000 : ℚ) : ℝ) + ((51:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-1089/25000 : ℚ)) : ℝ) 51).1,
    (cos_sin_shift (((-1089/25000 : ℚ)) : ℝ) 51).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_242_sign
end AxiomAudit
