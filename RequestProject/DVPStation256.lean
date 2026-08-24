import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 256` (rung-262.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT256 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((256 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((579807/1000000 : ℚ) : ℝ))

theorem st256_c1 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((104571/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -724759/5000000) (δ := 201/1000000000) (ψ := 579807/1000000) 256 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t1 : ((418259/500000 : ℚ) : ℝ) ≤ stT256 1 := by
  have hc : ((418259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418259/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((418259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c2 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((59247/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2341687/10000000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 28
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t2 : ((209452075607/500000000000 : ℚ) : ℝ) ≤ stT256 2 := by
  have hc : ((29621/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209452075607/500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((29621/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c3 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-486093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207841/400000) (δ := 6489/500000000) (ψ := 579807/1000000) 256 45
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t3 : ((-2806748068929/10000000000000 : ℚ) : ℝ) ≤ stT256 3 := by
  have hc : ((-486143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2806748068929/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-486143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c4 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-772249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6132923/10000000) (δ := 12999/1000000000) (ψ := 579807/1000000) 256 56
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t4 : ((-3861495772299/10000000000000 : ℚ) : ℝ) ≤ stT256 4 := by
  have hc : ((-772299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3861495772299/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-772299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c5 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-496849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3786579/5000000) (δ := 2567/200000000) (ψ := 579807/1000000) 256 65
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t5 : ((-138880506429/312500000000 : ℚ) : ℝ) ≤ stT256 5 := by
  have hc : ((-248437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138880506429/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-248437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c6 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((211559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -351197/2500000) (δ := 6413/500000000) (ψ := 579807/1000000) 256 73
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t6 : ((863634778413/2500000000000 : ℚ) : ℝ) ≤ stT256 6 := by
  have hc : ((423093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((863634778413/2500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((423093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c7 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((360911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75097/250000) (δ := 6467/500000000) (ψ := 579807/1000000) 256 79
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t7 : ((340981528371/2500000000000 : ℚ) : ℝ) ≤ stT256 7 := by
  have hc : ((360861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340981528371/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((360861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c8 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-338149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5783803/10000000) (δ := 807/62500000) (ψ := 579807/1000000) 256 85
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t8 : ((-298906418729/1250000000000 : ℚ) : ℝ) ≤ stT256 8 := by
  have hc : ((-169087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-298906418729/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-169087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c9 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-453349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 845683/1250000) (δ := 647/50000000) (ψ := 579807/1000000) 256 89
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t9 : ((-377811742229/1250000000000 : ℚ) : ℝ) ≤ stT256 9 := by
  have hc : ((-226687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377811742229/1250000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-226687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c10 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-82943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4343633/10000000) (δ := 12927/1000000000) (ψ := 579807/1000000) 256 94
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t10 : ((-16397992569/312500000000 : ℚ) : ℝ) ≤ stT256 10 := by
  have hc : ((-10371/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16397992569/312500000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-10371/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c11 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-783319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3088479/5000000) (δ := 6449/500000000) (ψ := 579807/1000000) 256 98
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t11 : ((-1180973419533/5000000000000 : ℚ) : ℝ) ≤ stT256 11 := by
  have hc : ((-783369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1180973419533/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-783369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c12 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((18061/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149153/625000) (δ := 811/62500000) (ψ := 579807/1000000) 256 101
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t12 : ((834129588201/5000000000000 : ℚ) : ℝ) ≤ stT256 12 := by
  have hc : ((288951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((834129588201/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((288951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c13 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-213699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6489887/10000000) (δ := 3237/250000000) (ψ := 579807/1000000) 256 104
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t13 : ((-1185458117923/5000000000000 : ℚ) : ℝ) ≤ stT256 13 := by
  have hc : ((-427423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1185458117923/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-427423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c14 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-911637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6795117/10000000) (δ := 1287/100000000) (ψ := 579807/1000000) 256 107
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t14 : ((-2436586528131/10000000000000 : ℚ) : ℝ) ≤ stT256 14 := by
  have hc : ((-911687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2436586528131/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-911687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c15 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((2507/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3826683/10000000) (δ := 3203/250000000) (ψ := 579807/1000000) 256 110
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t15 : ((12929950407/1250000000000 : ℚ) : ℝ) ≤ stT256 15 := by
  have hc : ((20031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12929950407/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((20031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c16 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((174709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1992567/10000000) (δ := 1289/100000000) (ψ := 579807/1000000) 256 113
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t16 : ((349393/2000000 : ℚ) : ℝ) ≤ stT256 16 := by
  have hc : ((349393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349393/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((349393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c17 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-276393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5391251/10000000) (δ := 12927/1000000000) (ψ := 579807/1000000) 256 115
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t17 : ((-335206165613/2500000000000 : ℚ) : ℝ) ≤ stT256 17 := by
  have hc : ((-138209/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335206165613/2500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-138209/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c18 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-470369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5151263/10000000) (δ := 12849/1000000000) (ψ := 579807/1000000) 256 118
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t18 : ((-1108788402637/10000000000000 : ℚ) : ℝ) ≤ stT256 18 := by
  have hc : ((-470419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1108788402637/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-470419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c19 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((706913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -982091/5000000) (δ := 647/50000000) (ψ := 579807/1000000) 256 120
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t19 : ((1621654699491/10000000000000 : ℚ) : ℝ) ≤ stT256 19 := by
  have hc : ((706863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1621654699491/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((706863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c20 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((121961/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138099/2500000) (δ := 12877/1000000000) (ψ := 579807/1000000) 256 122
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t20 : ((1090795967873/5000000000000 : ℚ) : ℝ) ≤ stT256 20 := by
  have hc : ((487819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1090795967873/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((487819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c21 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((59763/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148519/2000000) (δ := 12911/1000000000) (ψ := 579807/1000000) 256 124
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t21 : ((521626738031/2500000000000 : ℚ) : ℝ) ≤ stT256 21 := by
  have hc : ((478079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((521626738031/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((478079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c22 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((57819/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2385721/10000000) (δ := 6453/500000000) (ψ := 579807/1000000) 256 126
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t22 : ((61629926349/500000000000 : ℚ) : ℝ) ≤ stT256 22 := by
  have hc : ((28907/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61629926349/500000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((28907/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c23 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-269901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334531/625000) (δ := 12883/1000000000) (ψ := 579807/1000000) 256 128
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t23 : ((-56283484927/500000000000 : ℚ) : ℝ) ≤ stT256 23 := by
  have hc : ((-134963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56283484927/500000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-134963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c24 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-783499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1235537/2000000) (δ := 3207/250000000) (ψ := 579807/1000000) 256 129
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t24 : ((-799706563929/5000000000000 : ℚ) : ℝ) ≤ stT256 24 := by
  have hc : ((-783549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799706563929/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-783549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c25 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((937599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443919/5000000) (δ := 12961/1000000000) (ψ := 579807/1000000) 256 131
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t25 : ((937549/5000000 : ℚ) : ℝ) ≤ stT256 25 := by
  have hc : ((937549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((937549/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((937549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c26 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-564593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135671/250000) (δ := 1607/125000000) (ψ := 579807/1000000) 256 133
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t26 : ((-553678197583/5000000000000 : ℚ) : ℝ) ≤ stT256 26 := by
  have hc : ((-564643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553678197583/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-564643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c27 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((88817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3018989/10000000) (δ := 3241/250000000) (ψ := 579807/1000000) 256 134
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t27 : ((683617041/10000000000 : ℚ) : ℝ) ≤ stT256 27 := by
  have hc : ((177609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((683617041/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((177609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c28 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-459869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -512161/1000000) (δ := 513/40000000) (ψ := 579807/1000000) 256 136
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t28 : ((-869165504337/10000000000000 : ℚ) : ℝ) ≤ stT256 28 := by
  have hc : ((-459919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-869165504337/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-459919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c29 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((795149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628859/10000000) (δ := 2577/200000000) (ψ := 579807/1000000) 256 137
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t29 : ((1476461473347/10000000000000 : ℚ) : ℝ) ≤ stT256 29 := by
  have hc : ((795099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1476461473347/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((795099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c30 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-995543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119029/156250) (δ := 203/15625000) (ψ := 579807/1000000) 256 138
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t30 : ((-908847977503/5000000000000 : ℚ) : ℝ) ≤ stT256 30 := by
  have hc : ((-995593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-908847977503/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-995593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c31 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((107791/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -562507/2000000) (δ := 12807/1000000000) (ψ := 579807/1000000) 256 140
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t31 : ((387151796521/5000000000000 : ℚ) : ℝ) ≤ stT256 31 := by
  have hc : ((215557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387151796521/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((215557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c32 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((188039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179867/1000000) (δ := 6457/500000000) (ψ := 579807/1000000) 256 141
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t32 : ((332386853799/2500000000000 : ℚ) : ℝ) ≤ stT256 32 := by
  have hc : ((376053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332386853799/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((376053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c33 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-21141/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 578453/1000000) (δ := 6491/500000000) (ψ := 579807/1000000) 256 142
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t33 : ((-588871784337/5000000000000 : ℚ) : ℝ) ≤ stT256 33 := by
  have hc : ((-338281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-588871784337/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-338281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c34 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-862097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1631369/2500000) (δ := 2567/200000000) (ψ := 579807/1000000) 256 144
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t34 : ((-739285017471/5000000000000 : ℚ) : ℝ) ≤ stT256 34 := by
  have hc : ((-862147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-739285017471/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-862147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c35 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((98063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3681439/10000000) (δ := 12943/1000000000) (ψ := 579807/1000000) 256 145
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t35 : ((41418039501/2500000000000 : ℚ) : ℝ) ≤ stT256 35 := by
  have hc : ((98013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41418039501/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((98013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c36 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((21391/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1360027/10000000) (δ := 12953/1000000000) (ψ := 579807/1000000) 256 146
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t36 : ((71299138147/500000000000 : ℚ) : ℝ) ≤ stT256 36 := by
  have hc : ((85559/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71299138147/500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((85559/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c37 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((61411/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46737/1000000) (δ := 6423/500000000) (ψ := 579807/1000000) 256 147
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t37 : ((807630968107/5000000000000 : ℚ) : ℝ) ≤ stT256 37 := by
  have hc : ((491263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((807630968107/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((491263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c38 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((372313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365411/2000000) (δ := 201/15625000) (ψ := 579807/1000000) 256 148
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t38 : ((4718209419/39062500000 : ℚ) : ℝ) ≤ stT256 38 := by
  have hc : ((11634/15625 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4718209419/39062500000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((11634/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c39 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((455943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 685853/2500000) (δ := 12971/1000000000) (ψ := 579807/1000000) 256 149
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t39 : ((730012798933/10000000000000 : ℚ) : ℝ) ≤ stT256 39 := by
  have hc : ((455893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((730012798933/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((455893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c40 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((271797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80971/250000) (δ := 517/40000000) (ψ := 579807/1000000) 256 150
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t40 : ((214834754043/5000000000000 : ℚ) : ℝ) ≤ stT256 40 := by
  have hc : ((271747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214834754043/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((271747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c41 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((58731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3334141/10000000) (δ := 12817/1000000000) (ψ := 579807/1000000) 256 151
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t41 : ((183405708069/5000000000000 : ℚ) : ℝ) ≤ stT256 41 := by
  have hc : ((117437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183405708069/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((117437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c42 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((86039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1524321/5000000) (δ := 12893/1000000000) (ψ := 579807/1000000) 256 152
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t42 : ((265483456749/5000000000000 : ℚ) : ℝ) ≤ stT256 42 := by
  have hc : ((172053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265483456749/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((172053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c43 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((114691/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2400199/10000000) (δ := 13/1000000) (ψ := 579807/1000000) 256 153
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t43 : ((34977360957/400000000000 : ℚ) : ℝ) ≤ stT256 43 := by
  have hc : ((114681/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34977360957/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((114681/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c44 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((846081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 281103/2000000) (δ := 403/31250000) (ψ := 579807/1000000) 256 154
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t44 : ((318859777559/2500000000000 : ℚ) : ℝ) ≤ stT256 44 := by
  have hc : ((846031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318859777559/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((846031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c45 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((499743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5009/625000) (δ := 6407/500000000) (ψ := 579807/1000000) 256 155
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t45 : ((372467559749/2500000000000 : ℚ) : ℝ) ≤ stT256 45 := by
  have hc : ((249859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372467559749/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((249859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c46 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((405619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1561323/10000000) (δ := 6461/500000000) (ψ := 579807/1000000) 256 156
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t46 : ((299007749943/2500000000000 : ℚ) : ℝ) ≤ stT256 46 := by
  have hc : ((202797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299007749943/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((202797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c47 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((33579/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701051/2000000) (δ := 6487/500000000) (ψ := 579807/1000000) 256 157
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t47 : ((48965388281/2000000000000 : ℚ) : ℝ) ≤ stT256 47 := by
  have hc : ((33569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48965388281/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((33569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c48 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-663001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2869521/5000000) (δ := 12867/1000000000) (ψ := 579807/1000000) 256 158
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t48 : ((-59814493761/625000000000 : ℚ) : ℝ) ≤ stT256 48 := by
  have hc : ((-663051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59814493761/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-663051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c49 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-493717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3728623/5000000) (δ := 12867/1000000000) (ψ := 579807/1000000) 256 158
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t49 : ((-88168249553/625000000000 : ℚ) : ℝ) ≤ stT256 49 := by
  have hc : ((-246871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88168249553/625000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-246871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c50 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-296317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187163/400000) (δ := 12843/1000000000) (ψ := 579807/1000000) 256 159
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t50 : ((-209563180269/5000000000000 : ℚ) : ℝ) ≤ stT256 50 := by
  have hc : ((-296367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209563180269/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-296367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c51 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((98909/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205597/1250000) (δ := 259/20000000) (ψ := 579807/1000000) 256 160
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t51 : ((13849154277/125000000000 : ℚ) : ℝ) ≤ stT256 51 := by
  have hc : ((395611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13849154277/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((395611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c52 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((79351/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408901/2500000) (δ := 6473/500000000) (ψ := 579807/1000000) 256 161
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t52 : ((220066131/2000000000 : ℚ) : ℝ) ≤ stT256 52 := by
  have hc : ((39673/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220066131/2000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((39673/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c53 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-470883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5152719/10000000) (δ := 6419/500000000) (ψ := 579807/1000000) 256 162
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t53 : ((-323438197199/5000000000000 : ℚ) : ℝ) ≤ stT256 53 := by
  have hc : ((-470933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323438197199/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-470933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c54 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-114263/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272409/400000) (δ := 6419/500000000) (ψ := 579807/1000000) 256 162
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t54 : ((-155500794939/1250000000000 : ℚ) : ℝ) ≤ stT256 54 := by
  have hc : ((-457077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155500794939/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-457077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c55 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((209581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1422843/5000000) (δ := 1609/125000000) (ψ := 579807/1000000) 256 163
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t55 : ((70641275211/1250000000000 : ℚ) : ℝ) ≤ stT256 55 := by
  have hc : ((52389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70641275211/1250000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((52389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c56 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((430853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330437/10000000) (δ := 12979/1000000000) (ψ := 579807/1000000) 256 164
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t56 : ((71964755171/625000000000 : ℚ) : ℝ) ≤ stT256 56 := by
  have hc : ((107707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71964755171/625000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((107707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c57 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-654459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5710657/10000000) (δ := 12917/1000000000) (ψ := 579807/1000000) 256 165
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t57 : ((-866918769297/10000000000000 : ℚ) : ℝ) ≤ stT256 57 := by
  have hc : ((-654509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866918769297/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-654509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c58 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-140591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1084019/2000000) (δ := 12917/1000000000) (ψ := 579807/1000000) 256 165
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t58 : ((-73848613891/1000000000000 : ℚ) : ℝ) ≤ stT256 58 := by
  have hc : ((-281207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73848613891/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-281207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c59 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((966127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 163137/2500000) (δ := 1281/100000000) (ψ := 579807/1000000) 256 166
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t59 : ((1257725019453/10000000000000 : ℚ) : ℝ) ≤ stT256 59 := by
  have hc : ((966077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1257725019453/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((966077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c60 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-37051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4298871/10000000) (δ := 129/10000000) (ψ := 579807/1000000) 256 167
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t60 : ((-19139517273/1000000000000 : ℚ) : ℝ) ≤ stT256 60 := by
  have hc : ((-74127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19139517273/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-74127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c61 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-808239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6279881/10000000) (δ := 129/10000000) (ψ := 579807/1000000) 256 167
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t61 : ((-1034908178641/10000000000000 : ℚ) : ℝ) ≤ stT256 61 := by
  have hc : ((-808289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1034908178641/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-808289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c62 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((184871/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978637/10000000) (δ := 2599/200000000) (ψ := 579807/1000000) 256 168
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t62 : ((234773654861/2000000000000 : ℚ) : ℝ) ≤ stT256 62 := by
  have hc : ((184861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234773654861/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((184861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c63 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-111471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -448907/1000000) (δ := 1611/125000000) (ψ := 579807/1000000) 256 169
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t63 : ((-8779487717/312500000000 : ℚ) : ℝ) ≤ stT256 63 := by
  have hc : ((-13937/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8779487717/312500000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-13937/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c64 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-61717/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2794921/5000000) (δ := 1611/125000000) (ψ := 579807/1000000) 256 169
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t64 : ((-38576280861/500000000000 : ℚ) : ℝ) ≤ stT256 64 := by
  have hc : ((-30861/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38576280861/500000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-30861/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c65 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((498473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195433/10000000) (δ := 6411/500000000) (ψ := 579807/1000000) 256 170
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t65 : ((38640530091/312500000000 : ℚ) : ℝ) ≤ stT256 65 := by
  have hc : ((31153/31250 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38640530091/312500000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((31153/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c66 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-24127/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533049/2500000) (δ := 12929/1000000000) (ψ := 579807/1000000) 256 171
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t66 : ((-95040670431/1000000000000 : ℚ) : ℝ) ≤ stT256 66 := by
  have hc : ((-386057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95040670431/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-386057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c67 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((21637/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174603/500000) (δ := 12929/1000000000) (ψ := 579807/1000000) 256 171
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t67 : ((52852314981/2500000000000 : ℚ) : ℝ) ≤ stT256 67 := by
  have hc : ((86523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52852314981/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((86523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c68 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((91841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17089/62500) (δ := 12967/1000000000) (ψ := 579807/1000000) 256 172
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t68 : ((55680716709/1000000000000 : ℚ) : ℝ) ≤ stT256 68 := by
  have hc : ((91831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55680716709/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((91831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c69 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-439271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 206531/312500) (δ := 12967/1000000000) (ψ := 579807/1000000) 256 172
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t69 : ((-516455511/4882812500 : ℚ) : ℝ) ≤ stT256 69 := by
  have hc : ((-13728/15625 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-516455511/4882812500 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-13728/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c70 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((249759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109797/10000000) (δ := 12859/1000000000) (ψ := 579807/1000000) 256 173
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t70 : ((149252004851/1250000000000 : ℚ) : ℝ) ≤ stT256 70 := by
  have hc : ((499493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149252004851/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((499493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c71 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-86099/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3260011/5000000) (δ := 12851/1000000000) (ψ := 579807/1000000) 256 174
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t71 : ((-6386667333/62500000000 : ℚ) : ℝ) ≤ stT256 71 := by
  have hc : ((-10763/12500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6386667333/62500000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-10763/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c72 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((563249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243121/1000000) (δ := 12851/1000000000) (ψ := 579807/1000000) 256 174
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t72 : ((663736216689/10000000000000 : ℚ) : ℝ) ≤ stT256 72 := by
  have hc : ((563199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((663736216689/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((563199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c73 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-103653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4449041/10000000) (δ := 6479/500000000) (ψ := 579807/1000000) 256 175
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t73 : ((-15168246917/625000000000 : ℚ) : ℝ) ≤ stT256 73 := by
  have hc : ((-51839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15168246917/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-51839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c74 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-16529/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4258543/10000000) (δ := 6479/500000000) (ψ := 579807/1000000) 256 175
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t74 : ((-76887391257/5000000000000 : ℚ) : ℝ) ≤ stT256 74 := by
  have hc : ((-66141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76887391257/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-66141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c75 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((414453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2858637/10000000) (δ := 6469/500000000) (ψ := 579807/1000000) 256 176
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t75 : ((4785111441/100000000000 : ℚ) : ℝ) ≤ stT256 75 := by
  have hc : ((414403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4785111441/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((414403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c76 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-626083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5618291/10000000) (δ := 6469/500000000) (ψ := 579807/1000000) 256 176
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t76 : ((-718224015507/10000000000000 : ℚ) : ℝ) ≤ stT256 76 := by
  have hc : ((-626133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-718224015507/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-626133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c77 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((771621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215441/1250000) (δ := 12831/1000000000) (ψ := 579807/1000000) 256 177
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t77 : ((175857233891/2000000000000 : ℚ) : ℝ) ≤ stT256 77 := by
  have hc : ((771571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175857233891/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((771571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c78 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-863951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 816831/1250000) (δ := 12831/1000000000) (ψ := 579807/1000000) 256 177
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t78 : ((-489144662139/5000000000000 : ℚ) : ℝ) ≤ stT256 78 := by
  have hc : ((-864001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489144662139/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-864001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c79 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((45893/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204071/2000000) (δ := 12879/1000000000) (ψ := 579807/1000000) 256 178
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t79 : ((103261609947/1000000000000 : ℚ) : ℝ) ≤ stT256 79 := by
  have hc : ((91781/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103261609947/1000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((91781/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c80 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-118273/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7030077/10000000) (δ := 12879/1000000000) (ψ := 579807/1000000) 256 178
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t80 : ((-264480445989/2500000000000 : ℚ) : ℝ) ≤ stT256 80 := by
  have hc : ((-473117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264480445989/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-473117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c81 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((957959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -363743/5000000) (δ := 12987/1000000000) (ψ := 579807/1000000) 256 179
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t81 : ((1064343226899/10000000000000 : ℚ) : ℝ) ≤ stT256 81 := by
  have hc : ((957909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1064343226899/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((957909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c82 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-957831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3562689/5000000) (δ := 12987/1000000000) (ψ := 579807/1000000) 256 179
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t82 : ((-264450828599/2500000000000 : ℚ) : ℝ) ≤ stT256 82 := by
  have hc : ((-957881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264450828599/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-957881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c83 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((946057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82489/1000000) (δ := 12909/1000000000) (ψ := 579807/1000000) 256 180
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t83 : ((519188507747/5000000000000 : ℚ) : ℝ) ≤ stT256 83 := by
  have hc : ((946007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519188507747/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((946007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c84 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-229711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3419923/5000000) (δ := 25709/1000000000) (ψ := 579807/1000000) 256 180
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t84 : ((-50129802723/500000000000 : ℚ) : ℝ) ≤ stT256 84 := by
  have hc : ((-459447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50129802723/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-459447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c85 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((217249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1294069/10000000) (δ := 6401/500000000) (ψ := 579807/1000000) 256 181
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t85 : ((117813002099/1250000000000 : ℚ) : ℝ) ≤ stT256 85 := by
  have hc : ((434473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117813002099/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((434473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c86 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-786889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6191371/10000000) (δ := 6401/500000000) (ψ := 579807/1000000) 256 181
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t86 : ((-106072294749/1250000000000 : ℚ) : ℝ) ≤ stT256 86 := by
  have hc : ((-786939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106072294749/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-786939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c87 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((662199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132351/625000) (δ := 3227/250000000) (ψ := 579807/1000000) 256 182
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t87 : ((44368618043/625000000000 : ℚ) : ℝ) ≤ stT256 87 := by
  have hc : ((662149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44368618043/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((662149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c88 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-486347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324797/625000) (δ := 3227/250000000) (ψ := 579807/1000000) 256 182
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t88 : ((-129625286897/2500000000000 : ℚ) : ℝ) ≤ stT256 88 := by
  have hc : ((-486397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129625286897/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-486397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c89 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((128049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -819883/2500000) (δ := 3247/250000000) (ψ := 579807/1000000) 256 183
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t89 : ((16963131991/625000000000 : ℚ) : ℝ) ≤ stT256 89 := by
  have hc : ((16003/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16963131991/625000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((16003/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c90 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((11121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193569/500000) (δ := 3247/250000000) (ψ := 579807/1000000) 256 183
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t90 : ((365506401/156250000000 : ℚ) : ℝ) ≤ stT256 90 := by
  have hc : ((1387/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365506401/156250000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((1387/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c91 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-8221/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4764679/10000000) (δ := 321/12500000) (ψ := 579807/1000000) 256 184
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t91 : ((-6895409073/200000000000 : ℚ) : ℝ) ≤ stT256 91 := by
  have hc : ((-32889/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6895409073/200000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-32889/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c92 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((156971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2229913/10000000) (δ := 161/12500000) (ψ := 579807/1000000) 256 184
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t92 : ((81820268631/1250000000000 : ℚ) : ℝ) ≤ stT256 92 := by
  have hc : ((313917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81820268631/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((313917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c93 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-868829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3279537/5000000) (δ := 1283/100000000) (ψ := 579807/1000000) 256 185
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t93 : ((-112623227101/1250000000000 : ℚ) : ℝ) ≤ stT256 93 := by
  have hc : ((-868879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112623227101/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-868879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c94 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((993467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142959/5000000) (δ := 1283/100000000) (ψ := 579807/1000000) 256 185
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t94 : ((1024631155557/10000000000000 : ℚ) : ℝ) ≤ stT256 94 := by
  have hc : ((993417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1024631155557/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((993417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c95 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-474899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3529231/5000000) (δ := 1283/100000000) (ψ := 579807/1000000) 256 185
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t95 : ((-121815512649/1250000000000 : ℚ) : ℝ) ≤ stT256 95 := by
  have hc : ((-118731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121815512649/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-118731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c96 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((711513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1947869/10000000) (δ := 12937/1000000000) (ψ := 579807/1000000) 256 186
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t96 : ((36306668353/500000000000 : ℚ) : ℝ) ≤ stT256 96 := by
  have hc : ((711463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36306668353/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((711463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c97 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-298321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4684323/10000000) (δ := 12937/1000000000) (ψ := 579807/1000000) 256 186
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t97 : ((-302950099737/10000000000000 : ℚ) : ℝ) ≤ stT256 97 := by
  have hc : ((-298371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302950099737/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-298371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c98 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-211389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4459481/10000000) (δ := 12959/1000000000) (ψ := 579807/1000000) 256 187
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t98 : ((-213585740167/10000000000000 : ℚ) : ℝ) ≤ stT256 98 := by
  have hc : ((-211439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213585740167/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-211439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c99 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((685707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 407611/2000000) (δ := 12959/1000000000) (ψ := 579807/1000000) 256 187
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t99 : ((689110654309/10000000000000 : ℚ) : ℝ) ≤ stT256 99 := by
  have hc : ((685657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((689110654309/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((685657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c100 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-969771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1809429/2500000) (δ := 3213/250000000) (ψ := 579807/1000000) 256 188
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t100 : ((-969821/10000000 : ℚ) : ℝ) ≤ stT256 100 := by
  have hc : ((-969821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-969821/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-969821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c101 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((94013/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43473/500000) (δ := 3213/250000000) (ψ := 579807/1000000) 256 188
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t101 : ((11692679787/125000000000 : ℚ) : ℝ) ≤ stT256 101 := by
  have hc : ((11751/12500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11692679787/125000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((11751/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c102 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-567617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359003/2500000) (δ := 3213/250000000) (ψ := 579807/1000000) 256 188
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t102 : ((-140518586179/2500000000000 : ℚ) : ℝ) ≤ stT256 102 := by
  have hc : ((-567667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140518586179/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-567667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c103 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-40411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4028047/10000000) (δ := 6429/500000000) (ψ := 579807/1000000) 256 189
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t103 : ((-3986743713/1000000000000 : ℚ) : ℝ) ≤ stT256 103 := by
  have hc : ((-40461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3986743713/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-40461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c104 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((162687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2155569/10000000) (δ := 6429/500000000) (ψ := 579807/1000000) 256 189
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t104 : ((15951536121/250000000000 : ℚ) : ℝ) ≤ stT256 104 := by
  have hc : ((325349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15951536121/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((325349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c105 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-123189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3713957/5000000) (δ := 6483/500000000) (ψ := 579807/1000000) 256 190
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t105 : ((-480905470681/5000000000000 : ℚ) : ℝ) ≤ stT256 105 := by
  have hc : ((-492781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-480905470681/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-492781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c106 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((34213/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -680773/5000000) (δ := 6483/500000000) (ψ := 579807/1000000) 256 190
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t106 : ((6645726227/80000000000 : ℚ) : ℝ) ≤ stT256 106 := by
  have hc : ((34211/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6645726227/80000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((34211/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c107 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-142197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2323963/5000000) (δ := 6483/500000000) (ψ := 579807/1000000) 256 190
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t107 : ((-68745634807/2500000000000 : ℚ) : ℝ) ≤ stT256 107 := by
  have hc : ((-71111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68745634807/2500000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-71111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c108 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-227247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2553251/5000000) (δ := 1293/100000000) (ψ := 579807/1000000) 256 191
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t108 : ((-27336588659/625000000000 : ℚ) : ℝ) ≤ stT256 108 := by
  have hc : ((-28409/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27336588659/625000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-28409/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c109 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((475111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 396061/5000000) (δ := 1293/100000000) (ψ := 579807/1000000) 256 191
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t109 : ((113762430759/1250000000000 : ℚ) : ℝ) ≤ stT256 109 := by
  have hc : ((237543/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113762430759/1250000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((237543/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c110 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-883823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3318461/5000000) (δ := 1293/100000000) (ψ := 579807/1000000) 256 191
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t110 : ((-842740202199/10000000000000 : ℚ) : ℝ) ≤ stT256 110 := by
  have hc : ((-883873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-842740202199/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-883873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c111 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((256263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655821/2000000) (δ := 12823/1000000000) (ψ := 579807/1000000) 256 192
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t111 : ((243186362441/10000000000000 : ℚ) : ℝ) ≤ stT256 111 := by
  have hc : ((256213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243186362441/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((256213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c112 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((55343/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2460799/10000000) (δ := 12823/1000000000) (ψ := 579807/1000000) 256 192
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t112 : ((26144742459/500000000000 : ℚ) : ℝ) ≤ stT256 112 := by
  have hc : ((27669/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26144742459/500000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((27669/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c113 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-993009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1889551/2500000) (δ := 12887/1000000000) (ψ := 579807/1000000) 256 193
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t113 : ((-934191455539/10000000000000 : ℚ) : ℝ) ≤ stT256 113 := by
  have hc : ((-993059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-934191455539/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-993059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c114 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((719463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95971/500000) (δ := 12887/1000000000) (ψ := 579807/1000000) 256 193
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t114 : ((134758284921/2000000000000 : ℚ) : ℝ) ≤ stT256 114 := by
  have hc : ((719413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134758284921/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((719413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c115 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((25639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 917537/2500000) (δ := 12887/1000000000) (ψ := 579807/1000000) 256 193
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t115 : ((5974203439/625000000000 : ℚ) : ℝ) ≤ stT256 115 := by
  have hc : ((51253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5974203439/625000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((51253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c116 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-856207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1299339/2000000) (δ := 6497/500000000) (ψ := 579807/1000000) 256 194
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t116 : ((-795014930589/10000000000000 : ℚ) : ℝ) ≤ stT256 116 := by
  have hc : ((-856257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-795014930589/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-856257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c117 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((920583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1003063/10000000) (δ := 6497/500000000) (ψ := 579807/1000000) 256 194
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t117 : ((1702065517/20000000000 : ℚ) : ℝ) ≤ stT256 117 := by
  have hc : ((920533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1702065517/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((920533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c118 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-205249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 888757/2000000) (δ := 6497/500000000) (ψ := 579807/1000000) 256 194
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t118 : ((-7559725077/400000000000 : ℚ) : ℝ) ≤ stT256 118 := by
  have hc : ((-205299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7559725077/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-205299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c119 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-699389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5863347/10000000) (δ := 12901/1000000000) (ψ := 579807/1000000) 256 195
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t119 : ((-641175031861/10000000000000 : ℚ) : ℝ) ≤ stT256 119 := by
  have hc : ((-699439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641175031861/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-699439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c120 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((195891/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101527/2000000) (δ := 12901/1000000000) (ψ := 579807/1000000) 256 195
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t120 : ((17881388847/200000000000 : ℚ) : ℝ) ≤ stT256 120 := by
  have hc : ((195881/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17881388847/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((195881/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c121 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-343501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4803597/10000000) (δ := 12901/1000000000) (ψ := 579807/1000000) 256 195
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t121 : ((-312319122141/10000000000000 : ℚ) : ℝ) ≤ stT256 121 := by
  have hc : ((-343551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312319122141/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-343551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c122 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-631853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2818423/5000000) (δ := 12809/1000000000) (ψ := 579807/1000000) 256 196
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t122 : ((-286049218137/5000000000000 : ℚ) : ℝ) ≤ stT256 122 := by
  have hc : ((-631903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286049218137/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-631903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c123 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((986429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206167/5000000) (δ := 12809/1000000000) (ψ := 579807/1000000) 256 196
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t123 : ((889387366551/10000000000000 : ℚ) : ℝ) ≤ stT256 123 := by
  have hc : ((986379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((889387366551/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((986379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c124 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-165401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2384937/5000000) (δ := 12809/1000000000) (ψ := 579807/1000000) 256 196
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t124 : ((-74278507251/2500000000000 : ℚ) : ℝ) ≤ stT256 124 := by
  have hc : ((-82713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74278507251/2500000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-82713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c125 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-340159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5797481/10000000) (δ := 3229/250000000) (ψ := 579807/1000000) 256 197
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t125 : ((-9508440461/156250000000 : ℚ) : ℝ) ≤ stT256 125 := by
  have hc : ((-42523/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9508440461/156250000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-42523/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c126 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((192259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697833/10000000) (δ := 3229/250000000) (ψ := 579807/1000000) 256 197
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t126 : ((17126886663/200000000000 : ℚ) : ℝ) ≤ stT256 126 := by
  have hc : ((192249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17126886663/200000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((192249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c127 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-172903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4361431/10000000) (δ := 3229/250000000) (ψ := 579807/1000000) 256 197
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t127 : ((-153471055221/10000000000000 : ℚ) : ℝ) ≤ stT256 127 := by
  have hc : ((-172953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153471055221/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-172953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c128 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-819167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1265377/2000000) (δ := 649/50000000) (ψ := 579807/1000000) 256 198
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t128 : ((-181023199707/2500000000000 : ℚ) : ℝ) ≤ stT256 128 := by
  have hc : ((-819217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181023199707/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-819217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c129 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((858473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1346277/10000000) (δ := 649/50000000) (ψ := 579807/1000000) 256 198
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t129 : ((15115970607/200000000000 : ℚ) : ℝ) ≤ stT256 129 := by
  have hc : ((858423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15115970607/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((858423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c130 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((16511/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3595803/10000000) (δ := 649/50000000) (ψ := 579807/1000000) 256 198
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t130 : ((28951246051/2500000000000 : ℚ) : ℝ) ≤ stT256 130 := by
  have hc : ((66019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28951246051/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((66019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c131 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-120849/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225247/312500) (δ := 12873/1000000000) (ψ := 579807/1000000) 256 199
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t131 : ((-84473468961/1000000000000 : ℚ) : ℝ) ≤ stT256 131 := by
  have hc : ((-483421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84473468961/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-483421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c132 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((9261/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14631/62500) (δ := 12873/1000000000) (ψ := 579807/1000000) 256 199
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t132 : ((64479866219/1250000000000 : ℚ) : ℝ) ≤ stT256 132 := by
  have hc : ((296327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64479866219/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((296327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c133 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((135979/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77789/312500) (δ := 12873/1000000000) (ψ := 579807/1000000) 256 199
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t133 : ((235795551697/5000000000000 : ℚ) : ℝ) ≤ stT256 133 := by
  have hc : ((271933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235795551697/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((271933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c134 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-194811/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113801/156250) (δ := 25673/1000000000) (ψ := 579807/1000000) 256 199
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t134 : ((-168299822449/2000000000000 : ℚ) : ℝ) ≤ stT256 134 := by
  have hc : ((-194821/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168299822449/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-194821/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c135 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((4163/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3666331/10000000) (δ := 12837/1000000000) (ψ := 579807/1000000) 256 200
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t135 : ((1790607291/200000000000 : ℚ) : ℝ) ≤ stT256 135 := by
  have hc : ((4161/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1790607291/200000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((4161/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c136 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((182391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1056933/10000000) (δ := 12837/1000000000) (ψ := 579807/1000000) 256 200
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t136 : ((39097562113/500000000000 : ℚ) : ℝ) ≤ stT256 136 := by
  have hc : ((182381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39097562113/500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((182381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c137 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-332487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5745637/10000000) (δ := 12837/1000000000) (ψ := 579807/1000000) 256 200
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t137 : ((-4438816989/78125000000 : ℚ) : ℝ) ≤ stT256 137 := by
  have hc : ((-10391/15625 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4438816989/78125000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-10391/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c138 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-262333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2653899/5000000) (δ := 2589/200000000) (ψ := 579807/1000000) 256 201
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t138 : ((-111667042003/2500000000000 : ℚ) : ℝ) ≤ stT256 138 := by
  have hc : ((-131179/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111667042003/2500000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-131179/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c139 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((962501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343403/5000000) (δ := 2589/200000000) (ψ := 579807/1000000) 256 201
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t139 : ((204084847197/2500000000000 : ℚ) : ℝ) ≤ stT256 139 := by
  have hc : ((962451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204084847197/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((962451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c140 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((10383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1950517/5000000) (δ := 2589/200000000) (ψ := 579807/1000000) 256 201
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t140 : ((4366488141/5000000000000 : ℚ) : ℝ) ≤ stT256 140 := by
  have hc : ((10333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4366488141/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((10333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c141 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-97113/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3625897/5000000) (δ := 12951/1000000000) (ψ := 579807/1000000) 256 202
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t141 : ((-5111757371/62500000000 : ℚ) : ℝ) ≤ stT256 141 := by
  have hc : ((-48559/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5111757371/62500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-48559/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c142 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((230571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1364393/5000000) (δ := 12951/1000000000) (ψ := 579807/1000000) 256 202
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t142 : ((96734911413/2500000000000 : ℚ) : ℝ) ≤ stT256 142 := by
  have hc : ((115273/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96734911413/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((115273/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c143 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((761617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881239/5000000) (δ := 12951/1000000000) (ψ := 579807/1000000) 256 202
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t143 : ((318427155607/5000000000000 : ℚ) : ℝ) ≤ stT256 143 := by
  have hc : ((761567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318427155607/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((761567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c144 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-794483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3111191/5000000) (δ := 12951/1000000000) (ψ := 579807/1000000) 256 202
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t144 : ((-331055681511/5000000000000 : ℚ) : ℝ) ≤ stT256 144 := by
  have hc : ((-794533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331055681511/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-794533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c145 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-17463/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5056461/10000000) (δ := 3211/250000000) (ψ := 579807/1000000) 256 203
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t145 : ((-580155863/16000000000 : ℚ) : ℝ) ≤ stT256 145 := by
  have hc : ((-3493/8000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580155863/16000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-3493/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c146 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((965583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131561/2000000) (δ := 3211/250000000) (ψ := 579807/1000000) 256 203
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t146 : ((159815987693/2000000000000 : ℚ) : ℝ) ≤ stT256 146 := by
  have hc : ((965533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159815987693/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((965533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c147 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((4319/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3710771/10000000) (δ := 3211/250000000) (ψ := 579807/1000000) 256 203
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t147 : ((3560188769/500000000000 : ℚ) : ℝ) ≤ stT256 147 := by
  have hc : ((8633/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3560188769/500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((8633/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c148 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-199387/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -957273/1250000) (δ := 6433/500000000) (ψ := 579807/1000000) 256 204
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t148 : ((-32780667403/400000000000 : ℚ) : ℝ) ≤ stT256 148 := by
  have hc : ((-199397/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32780667403/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-199397/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c149 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((229391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83709/250000) (δ := 6433/500000000) (ψ := 579807/1000000) 256 204
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t149 : ((187883256771/10000000000000 : ℚ) : ℝ) ≤ stT256 149 := by
  have hc : ((229341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187883256771/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((229341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c150 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((931233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116567/1250000) (δ := 6433/500000000) (ψ := 579807/1000000) 256 204
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t150 : ((47519199673/625000000000 : ℚ) : ℝ) ≤ stT256 150 := by
  have hc : ((931183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47519199673/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((931183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c151 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-482263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129627/250000) (δ := 6433/500000000) (ψ := 579807/1000000) 256 204
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t151 : ((-392501013957/10000000000000 : ℚ) : ℝ) ≤ stT256 151 := by
  have hc : ((-482313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-392501013957/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-482313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c152 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-812587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1259687/2000000) (δ := 12973/1000000000) (ψ := 579807/1000000) 256 205
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t152 : ((-164784092949/2500000000000 : ℚ) : ℝ) ≤ stT256 152 := by
  have hc : ((-812637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164784092949/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-812637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c153 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((666957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2101699/10000000) (δ := 12973/1000000000) (ψ := 579807/1000000) 256 205
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t153 : ((134790574491/2500000000000 : ℚ) : ℝ) ≤ stT256 153 := by
  have hc : ((666907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134790574491/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((666907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c154 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((27081/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2067709/10000000) (δ := 12973/1000000000) (ψ := 579807/1000000) 256 205
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t154 : ((10910426969/200000000000 : ℚ) : ℝ) ≤ stT256 154 := by
  have hc : ((27079/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10910426969/200000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((27079/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c155 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-791493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6210109/10000000) (δ := 12973/1000000000) (ψ := 579807/1000000) 256 205
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t155 : ((-31789158423/500000000000 : ℚ) : ℝ) ≤ stT256 155 := by
  have hc : ((-791543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31789158423/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-791543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c156 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-21989/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5382079/10000000) (δ := 12923/1000000000) (ψ := 579807/1000000) 256 206
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t156 : ((-17606896231/400000000000 : ℚ) : ℝ) ≤ stT256 156 := by
  have hc : ((-21991/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17606896231/400000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-21991/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c157 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((173857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1292607/10000000) (δ := 12923/1000000000) (ψ := 579807/1000000) 256 206
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t157 : ((69372428421/1000000000000 : ℚ) : ℝ) ≤ stT256 157 := by
  have hc : ((173847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69372428421/1000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((173847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c158 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((446137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2770881/10000000) (δ := 12923/1000000000) (ψ := 579807/1000000) 256 206
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t158 : ((354887635459/10000000000000 : ℚ) : ℝ) ≤ stT256 158 := by
  have hc : ((446087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354887635459/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((446087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c159 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-228467/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6808769/10000000) (δ := 12923/1000000000) (ψ := 579807/1000000) 256 206
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t159 : ((-90598062217/1250000000000 : ℚ) : ℝ) ≤ stT256 159 := by
  have hc : ((-456959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90598062217/1250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-456959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c160 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-187253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97733/200000) (δ := 2563/200000000) (ψ := 579807/1000000) 256 207
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t160 : ((-7402818423/250000000000 : ℚ) : ℝ) ≤ stT256 160 := by
  have hc : ((-93639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7402818423/250000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-93639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c161 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((936019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89913/1000000) (δ := 2563/200000000) (ψ := 579807/1000000) 256 207
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t161 : ((73764652859/1000000000000 : ℚ) : ℝ) ≤ stT256 161 := by
  have hc : ((935969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73764652859/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((935969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c162 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((84619/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2451/8000) (δ := 2563/200000000) (ψ := 579807/1000000) 256 207
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t162 : ((66473127281/2500000000000 : ℚ) : ℝ) ≤ stT256 162 := by
  have hc : ((169213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66473127281/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((169213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c163 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-942523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3501123/5000000) (δ := 2563/200000000) (ψ := 579807/1000000) 256 207
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t163 : ((-738280670553/10000000000000 : ℚ) : ℝ) ≤ stT256 163 := by
  have hc : ((-942573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-738280670553/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-942573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c164 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-21181/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4791349/10000000) (δ := 2579/200000000) (ψ := 579807/1000000) 256 208
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t164 : ((-132336212037/5000000000000 : ℚ) : ℝ) ≤ stT256 164 := by
  have hc : ((-169473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132336212037/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-169473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c165 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((467893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900789/10000000) (δ := 2579/200000000) (ψ := 579807/1000000) 256 208
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t165 : ((45529287783/625000000000 : ℚ) : ℝ) ≤ stT256 165 := by
  have hc : ((116967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45529287783/625000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((116967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c166 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((74979/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2966283/10000000) (δ := 2579/200000000) (ψ := 579807/1000000) 256 208
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t166 : ((1163743787/40000000000 : ℚ) : ℝ) ≤ stT256 166 := by
  have hc : ((74969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1163743787/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((74969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c167 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-457049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6810187/10000000) (δ := 2579/200000000) (ψ := 579807/1000000) 256 208
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t167 : ((-2763240867/39062500000 : ℚ) : ℝ) ≤ stT256 167 := by
  have hc : ((-228537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2763240867/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-228537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c168 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-5549/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5076913/10000000) (δ := 13001/1000000000) (ψ := 579807/1000000) 256 209
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t168 : ((-34253040249/1000000000000 : ℚ) : ℝ) ≤ stT256 168 := by
  have hc : ((-44397/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34253040249/1000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-44397/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c169 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((872033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278641/10000000) (δ := 13001/1000000000) (ψ := 579807/1000000) 256 209
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t169 : ((67075548309/1000000000000 : ℚ) : ℝ) ≤ stT256 169 := by
  have hc : ((871983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67075548309/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((871983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c170 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((67657/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2497167/10000000) (δ := 13001/1000000000) (ψ := 579807/1000000) 256 209
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t170 : ((51885689823/1250000000000 : ℚ) : ℝ) ≤ stT256 170 := by
  have hc : ((270603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51885689823/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((270603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c171 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-801343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6250831/10000000) (δ := 13001/1000000000) (ψ := 579807/1000000) 256 209
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t171 : ((-7660515687/125000000000 : ℚ) : ℝ) ≤ stT256 171 := by
  have hc : ((-801393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7660515687/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-801393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c172 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-658893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1431339/2500000) (δ := 6447/500000000) (ψ := 579807/1000000) 256 210
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t172 : ((-502439424899/10000000000000 : ℚ) : ℝ) ≤ stT256 172 := by
  have hc : ((-658943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502439424899/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-658943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c173 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((692329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503803/2500000) (δ := 6447/500000000) (ψ := 579807/1000000) 256 210
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t173 : ((105265867903/2000000000000 : ℚ) : ℝ) ≤ stT256 173 := by
  have hc : ((692279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105265867903/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((692279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c174 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((39209/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418389/2500000) (δ := 6447/500000000) (ψ := 579807/1000000) 256 210
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t174 : ((29722369237/500000000000 : ℚ) : ℝ) ≤ stT256 174 := by
  have hc : ((78413/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29722369237/500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((78413/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c175 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-267997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1335301/2500000) (δ := 6447/500000000) (ψ := 579807/1000000) 256 210
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t175 : ((-101302801219/2500000000000 : ℚ) : ℝ) ≤ stT256 175 := by
  have hc : ((-134011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101302801219/2500000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-134011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c176 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-179777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6720039/10000000) (δ := 801/62500000) (ψ := 579807/1000000) 256 211
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t176 : ((-135519665073/2000000000000 : ℚ) : ℝ) ≤ stT256 176 := by
  have hc : ((-179787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135519665073/2000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-179787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c177 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((327093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3093927/10000000) (δ := 801/62500000) (ψ := 579807/1000000) 256 211
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t177 : ((122910281389/5000000000000 : ℚ) : ℝ) ≤ stT256 177 := by
  have hc : ((327043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122910281389/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((327043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c178 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((489563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102341/2000000) (δ := 801/62500000) (ψ := 579807/1000000) 256 211
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t178 : ((183461953339/2500000000000 : ℚ) : ℝ) ≤ stT256 178 := by
  have hc : ((244769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183461953339/2500000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((244769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c179 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-34011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4097177/10000000) (δ := 801/62500000) (ψ := 579807/1000000) 256 211
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t179 : ((-1589983231/312500000000 : ℚ) : ℝ) ≤ stT256 179 := by
  have hc : ((-8509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1589983231/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-8509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c180 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-62317/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7662617/10000000) (δ := 801/62500000) (ψ := 579807/1000000) 256 211
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t180 : ((-92901358179/1250000000000 : ℚ) : ℝ) ≤ stT256 180 := by
  have hc : ((-498561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92901358179/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-498561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c181 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-227053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2249809/5000000) (δ := 3231/250000000) (ψ := 579807/1000000) 256 212
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t181 : ((-33760904877/2000000000000 : ℚ) : ℝ) ≤ stT256 181 := by
  have hc : ((-227103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33760904877/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-227103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c182 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((925141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486737/5000000) (δ := 3231/250000000) (ψ := 579807/1000000) 256 212
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t182 : ((685722778659/10000000000000 : ℚ) : ℝ) ≤ stT256 182 := by
  have hc : ((925091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((685722778659/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((925091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c183 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((52901/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1266703/5000000) (δ := 3231/250000000) (ψ := 579807/1000000) 256 212
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t183 : ((1221932313/31250000000 : ℚ) : ℝ) ≤ stT256 183 := by
  have hc : ((1653/3125 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1221932313/31250000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((1653/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c184 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-371541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120423/200000) (δ := 3231/250000000) (ψ := 579807/1000000) 256 212
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t184 : ((-13696108543/250000000000 : ℚ) : ℝ) ≤ stT256 184 := by
  have hc : ((-185783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13696108543/250000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-185783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c185 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-396703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124359/200000) (δ := 3243/250000000) (ψ := 579807/1000000) 256 213
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t185 : ((-7292009413/125000000000 : ℚ) : ℝ) ≤ stT256 185 := by
  have hc : ((-49591/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7292009413/125000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-49591/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c186 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((223613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1383919/5000000) (δ := 3243/250000000) (ψ := 579807/1000000) 256 213
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t186 : ((8197127359/250000000000 : ℚ) : ℝ) ≤ stT256 186 := by
  have hc : ((55897/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8197127359/250000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((55897/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c187 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((120619/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 331921/5000000) (δ := 3243/250000000) (ψ := 579807/1000000) 256 213
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t187 : ((44100363459/625000000000 : ℚ) : ℝ) ≤ stT256 187 := by
  have hc : ((482451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44100363459/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((482451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c188 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-60029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2038577/5000000) (δ := 3243/250000000) (ψ := 579807/1000000) 256 213
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t188 : ((-1752684667/400000000000 : ℚ) : ℝ) ≤ stT256 188 := by
  have hc : ((-60079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1752684667/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-60079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c189 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-7907/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3736209/5000000) (δ := 3243/250000000) (ψ := 579807/1000000) 256 213
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t189 : ((-28758937041/400000000000 : ℚ) : ℝ) ≤ stT256 189 := by
  have hc : ((-39537/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28758937041/400000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-39537/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c190 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-181977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -971653/2000000) (δ := 2573/200000000) (ψ := 579807/1000000) 256 214
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t190 : ((-66019132477/2500000000000 : ℚ) : ℝ) ≤ stT256 190 := by
  have hc : ((-91001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66019132477/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-91001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c191 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((825641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1498649/10000000) (δ := 2573/200000000) (ψ := 579807/1000000) 256 214
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t191 : ((298688091117/5000000000000 : ℚ) : ℝ) ≤ stT256 191 := by
  have hc : ((825591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298688091117/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((825591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c192 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((148051/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1843367/10000000) (δ := 2573/200000000) (ψ := 579807/1000000) 256 214
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t192 : ((106839265167/2000000000000 : ℚ) : ℝ) ≤ stT256 192 := by
  have hc : ((148041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106839265167/2000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((148041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c193 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-11907/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5168039/10000000) (δ := 2573/200000000) (ψ := 579807/1000000) 256 214
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t193 : ((-4285874441/125000000000 : ℚ) : ℝ) ≤ stT256 193 := by
  have hc : ((-47633/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4285874441/125000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-47633/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c194 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-3877/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1808101/2500000) (δ := 2569/200000000) (ψ := 579807/1000000) 256 215
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t194 : ((-6959176587/100000000000 : ℚ) : ℝ) ≤ stT256 194 := by
  have hc : ((-9693/10000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6959176587/100000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-9693/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c195 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-5967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -985477/2500000) (δ := 2569/200000000) (ψ := 579807/1000000) 256 215
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t195 : ((-861772791/2000000000000 : ℚ) : ℝ) ≤ stT256 195 := by
  have hc : ((-6017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-861772791/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-6017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c196 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((120561/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167061/2500000) (δ := 2569/200000000) (ψ := 579807/1000000) 256 215
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t196 : ((68888359683/1000000000000 : ℚ) : ℝ) ≤ stT256 196 := by
  have hc : ((482219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68888359683/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((482219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c197 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((255043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129439/500000) (δ := 2569/200000000) (ψ := 579807/1000000) 256 215
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t197 : ((9084633723/250000000000 : ℚ) : ℝ) ≤ stT256 197 := by
  have hc : ((127509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9084633723/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((127509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c198 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-172397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1457323/2500000) (δ := 2569/200000000) (ψ := 579807/1000000) 256 215
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t198 : ((-24505251873/500000000000 : ℚ) : ℝ) ≤ stT256 198 := by
  have hc : ((-344819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24505251873/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-344819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c199 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-887087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6654479/10000000) (δ := 1619/125000000) (ψ := 579807/1000000) 256 216
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t199 : ((-314437725417/5000000000000 : ℚ) : ℝ) ≤ stT256 199 := by
  have hc : ((-887137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314437725417/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-887137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c200 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((191023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3446479/10000000) (δ := 1619/125000000) (ψ := 579807/1000000) 256 216
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t200 : ((67519077069/5000000000000 : ℚ) : ℝ) ≤ stT256 200 := by
  have hc : ((190973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67519077069/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((190973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c201 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((497413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50883/2000000) (δ := 1619/125000000) (ψ := 579807/1000000) 256 216
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t201 : ((17541506943/250000000000 : ℚ) : ℝ) ≤ stT256 201 := by
  have hc : ((124347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17541506943/250000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((124347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c202 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((195681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2921713/10000000) (δ := 1619/125000000) (ψ := 579807/1000000) 256 216
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t202 : ((17207871829/625000000000 : ℚ) : ℝ) ≤ stT256 202 := by
  have hc : ((24457/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17207871829/625000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((24457/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c203 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-759207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243289/400000) (δ := 1619/125000000) (ψ := 579807/1000000) 256 216
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t203 : ((-532894395791/10000000000000 : ℚ) : ℝ) ≤ stT256 203 := by
  have hc : ((-759257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-532894395791/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-759257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c204 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-8529/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6480779/10000000) (δ := 809/62500000) (ψ := 579807/1000000) 256 217
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t204 : ((-11943705319/200000000000 : ℚ) : ℝ) ≤ stT256 204 := by
  have hc : ((-17059/20000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11943705319/200000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-17059/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c205 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((114147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3351179/10000000) (δ := 809/62500000) (ψ := 579807/1000000) 256 217
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t205 : ((3985311423/250000000000 : ℚ) : ℝ) ≤ stT256 205 := by
  have hc : ((57061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3985311423/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((57061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c206 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((995517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236811/10000000) (δ := 809/62500000) (ψ := 579807/1000000) 256 217
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t206 : ((693574709311/10000000000000 : ℚ) : ℝ) ≤ stT256 206 := by
  have hc : ((995467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((693574709311/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((995467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c207 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((413063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2862453/10000000) (δ := 809/62500000) (ψ := 579807/1000000) 256 217
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t207 : ((35882982453/1250000000000 : ℚ) : ℝ) ≤ stT256 207 := by
  have hc : ((413013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35882982453/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((413013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c208 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-144571/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1189361/2000000) (δ := 809/62500000) (ψ := 579807/1000000) 256 217
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t208 : ((-783195277/15625000000 : ℚ) : ℝ) ≤ stT256 208 := by
  have hc : ((-144581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-783195277/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-144581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c209 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-893841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669159/1000000) (δ := 3209/250000000) (ψ := 579807/1000000) 256 218
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t209 : ((-123663562613/2000000000000 : ℚ) : ℝ) ≤ stT256 209 := by
  have hc : ((-893891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123663562613/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-893891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c210 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((14483/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1818339/5000000) (δ := 3209/250000000) (ψ := 579807/1000000) 256 218
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t210 : ((7991918791/1000000000000 : ℚ) : ℝ) ≤ stT256 210 := by
  have hc : ((57907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7991918791/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((57907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c211 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((971689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298147/5000000) (δ := 3209/250000000) (ψ := 579807/1000000) 256 218
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t211 : ((167225873373/2500000000000 : ℚ) : ℝ) ≤ stT256 211 := by
  have hc : ((971639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167225873373/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((971639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c212 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((563751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242969/1000000) (δ := 3209/250000000) (ψ := 579807/1000000) 256 218
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t212 : ((193575487101/5000000000000 : ℚ) : ℝ) ≤ stT256 212 := by
  have hc : ((563701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193575487101/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((563701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c213 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-142353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2720733/5000000) (δ := 3209/250000000) (ψ := 579807/1000000) 256 218
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t213 : ((-195094549159/5000000000000 : ℚ) : ℝ) ≤ stT256 213 := by
  have hc : ((-284731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195094549159/5000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-284731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c214 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-97273/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7268801/10000000) (δ := 6437/500000000) (ψ := 579807/1000000) 256 219
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t214 : ((-16624469727/250000000000 : ℚ) : ℝ) ≤ stT256 214 := by
  have hc : ((-48639/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16624469727/250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-48639/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c215 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-142763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4285121/10000000) (δ := 6437/500000000) (ψ := 579807/1000000) 256 219
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t215 : ((-19479550387/2000000000000 : ℚ) : ℝ) ≤ stT256 215 := by
  have hc : ((-142813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19479550387/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-142813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c216 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((864769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263053/2000000) (δ := 6437/500000000) (ψ := 579807/1000000) 256 219
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t216 : ((588366048947/10000000000000 : ℚ) : ℝ) ≤ stT256 216 := by
  have hc : ((864719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588366048947/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((864719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c217 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((198059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1640831/10000000) (δ := 6437/500000000) (ψ := 579807/1000000) 256 219
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t217 : ((67221339123/1250000000000 : ℚ) : ℝ) ≤ stT256 217 := by
  have hc : ((396093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67221339123/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((396093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c218 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-259541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4583359/10000000) (δ := 6437/500000000) (ψ := 579807/1000000) 256 219
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t218 : ((-87908675013/5000000000000 : ℚ) : ℝ) ≤ stT256 218 := by
  have hc : ((-259591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87908675013/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-259591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c219 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-990683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7512447/10000000) (δ := 6437/500000000) (ψ := 579807/1000000) 256 219
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t219 : ((-334737967977/5000000000000 : ℚ) : ℝ) ≤ stT256 219 := by
  have hc : ((-990733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334737967977/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-990733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c220 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-515101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1319951/2500000) (δ := 12981/1000000000) (ψ := 579807/1000000) 256 220
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t220 : ((-1736574021/50000000000 : ℚ) : ℝ) ≤ stT256 220 := by
  have hc : ((-515151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1736574021/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-515151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c221 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((290471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594319/2500000) (δ := 12981/1000000000) (ψ := 579807/1000000) 256 220
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t221 : ((3052732683/78125000000 : ℚ) : ℝ) ≤ stT256 221 := by
  have hc : ((145223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3052732683/78125000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((145223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c222 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((122387/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128017/2500000) (δ := 12981/1000000000) (ψ := 579807/1000000) 256 220
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t222 : ((82136574647/1250000000000 : ℚ) : ℝ) ≤ stT256 222 := by
  have hc : ((489523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82136574647/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((489523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c223 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((213741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847121/2500000) (δ := 12981/1000000000) (ψ := 579807/1000000) 256 220
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t223 : ((143097964459/10000000000000 : ℚ) : ℝ) ≤ stT256 223 := by
  have hc : ((213691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143097964459/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((213691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c224 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-801631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1563009/2500000) (δ := 12981/1000000000) (ψ := 579807/1000000) 256 220
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t224 : ((-267823183437/5000000000000 : ℚ) : ℝ) ≤ stT256 224 := by
  have hc : ((-801681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267823183437/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-801681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c225 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-877799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -825639/1250000) (δ := 2583/200000000) (ψ := 579807/1000000) 256 221
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t225 : ((-585232959283/10000000000000 : ℚ) : ℝ) ≤ stT256 225 := by
  have hc : ((-877849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-585232959283/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-877849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c226 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((63953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3767/10000) (δ := 5143/200000000) (ψ := 579807/1000000) 256 221
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t226 : ((4250763657/1000000000000 : ℚ) : ℝ) ≤ stT256 226 := by
  have hc : ((63903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4250763657/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((63903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c227 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((46497/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117671/1250000) (δ := 2583/200000000) (ψ := 579807/1000000) 256 221
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t227 : ((61718938047/1000000000000 : ℚ) : ℝ) ≤ stT256 227 := by
  have hc : ((92989/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61718938047/1000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((92989/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c228 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((183139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233977/1250000) (δ := 2583/200000000) (ψ := 579807/1000000) 256 221
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t228 : ((121278454649/2500000000000 : ℚ) : ℝ) ≤ stT256 228 := by
  have hc : ((366253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121278454649/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((366253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c229 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-58777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 584089/1250000) (δ := 2583/200000000) (ψ := 579807/1000000) 256 221
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t229 : ((-38847566553/2000000000000 : ℚ) : ℝ) ≤ stT256 229 := by
  have hc : ((-58787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38847566553/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-58787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c230 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-197539/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 932673/1250000) (δ := 2583/200000000) (ψ := 579807/1000000) 256 221
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t230 : ((-130260057169/2000000000000 : ℚ) : ℝ) ≤ stT256 230 := by
  have hc : ((-197549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130260057169/2000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-197549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c231 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-289379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5470003/10000000) (δ := 1601/125000000) (ψ := 579807/1000000) 256 222
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t231 : ((-1487608911/39062500000 : ℚ) : ℝ) ≤ stT256 231 := by
  have hc : ((-72351/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1487608911/39062500000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-72351/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c232 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((469401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2705459/10000000) (δ := 1601/125000000) (ψ := 579807/1000000) 256 222
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t232 : ((77035987683/2500000000000 : ℚ) : ℝ) ≤ stT256 232 := by
  have hc : ((469351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77035987683/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((469351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c233 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((999821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9449/2000000) (δ := 1601/125000000) (ψ := 579807/1000000) 256 222
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t233 : ((654970977291/10000000000000 : ℚ) : ℝ) ≤ stT256 233 := by
  have hc : ((999771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((654970977291/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((999771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c234 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((6874/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2788173/10000000) (δ := 1601/125000000) (ψ := 579807/1000000) 256 222
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t234 : ((3594528449/125000000000 : ℚ) : ℝ) ≤ stT256 234 := by
  have hc : ((219943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3594528449/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((219943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c235 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-59411/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5517389/10000000) (δ := 1601/125000000) (ψ := 579807/1000000) 256 222
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t235 : ((-4844847483/125000000000 : ℚ) : ℝ) ≤ stT256 235 := by
  have hc : ((-7427/12500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4844847483/125000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-7427/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c236 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-988407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3736471/5000000) (δ := 12903/1000000000) (ψ := 579807/1000000) 256 223
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t236 : ((-128686228373/2000000000000 : ℚ) : ℝ) ≤ stT256 236 := by
  have hc : ((-988457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128686228373/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-988457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c237 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-329653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -476683/1000000) (δ := 12903/1000000000) (ψ := 579807/1000000) 256 223
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t237 : ((-21416517771/1000000000000 : ℚ) : ℝ) ≤ stT256 237 := by
  have hc : ((-329703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21416517771/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-329703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c238 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((42233/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207211/1000000) (δ := 12903/1000000000) (ψ := 579807/1000000) 256 223
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t238 : ((218988253317/5000000000000 : ℚ) : ℝ) ≤ stT256 238 := by
  have hc : ((337839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218988253317/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((337839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c239 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((970249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305673/5000000) (δ := 12903/1000000000) (ψ := 579807/1000000) 256 223
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t239 : ((313784671177/5000000000000 : ℚ) : ℝ) ≤ stT256 239 := by
  have hc : ((970199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313784671177/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((970199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c240 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((63631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1641801/5000000) (δ := 12903/1000000000) (ψ := 579807/1000000) 256 223
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t240 : ((82131101789/5000000000000 : ℚ) : ℝ) ≤ stT256 240 := by
  have hc : ((127237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82131101789/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((127237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c241 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-722279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2972361/5000000) (δ := 12903/1000000000) (ψ := 579807/1000000) 256 223
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t241 : ((-465293281653/10000000000000 : ℚ) : ℝ) ≤ stT256 241 := by
  have hc : ((-722329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465293281653/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-722329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c242 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-239103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711313/1000000) (δ := 12993/1000000000) (ψ := 579807/1000000) 256 224
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t242 : ((-12296753703/200000000000 : ℚ) : ℝ) ≤ stT256 242 := by
  have hc : ((-478231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12296753703/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-478231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c243 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-217047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2236981/5000000) (δ := 12993/1000000000) (ψ := 579807/1000000) 256 224
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t243 : ((-139267942597/10000000000000 : ℚ) : ℝ) ≤ stT256 243 := by
  have hc : ((-217097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139267942597/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-217097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c244 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((739651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184561/1000000) (δ := 12993/1000000000) (ψ := 579807/1000000) 256 224
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t244 : ((59185090823/1250000000000 : ℚ) : ℝ) ≤ stT256 244 := by
  have hc : ((739601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59185090823/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((739601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c245 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((14886/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385979/5000000) (δ := 25793/1000000000) (ψ := 579807/1000000) 256 224
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t245 : ((76078472113/1250000000000 : ℚ) : ℝ) ≤ stT256 245 := by
  have hc : ((476327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76078472113/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((476327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c246 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((54371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1689451/5000000) (δ := 12993/1000000000) (ψ := 579807/1000000) 256 224
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t246 : ((8664418749/625000000000 : ℚ) : ℝ) ≤ stT256 246 := by
  have hc : ((108717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8664418749/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((108717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c247 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-45667/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2987627/5000000) (δ := 12993/1000000000) (ψ := 579807/1000000) 256 224
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t247 : ((-46494744777/1000000000000 : ℚ) : ℝ) ≤ stT256 247 := by
  have hc : ((-365361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46494744777/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-365361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c248 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-120033/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7146853/10000000) (δ := 6443/500000000) (ψ := 579807/1000000) 256 225
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t248 : ((-304900175157/5000000000000 : ℚ) : ℝ) ≤ stT256 248 := by
  have hc : ((-480157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304900175157/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-480157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c249 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-25493/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4571429/10000000) (δ := 6443/500000000) (ψ := 579807/1000000) 256 225
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t249 : ((-323174401/20000000000 : ℚ) : ℝ) ≤ stT256 249 := by
  have hc : ((-12749/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323174401/20000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-12749/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c250 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((694913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401249/2000000) (δ := 6443/500000000) (ψ := 579807/1000000) 256 225
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t250 : ((87893915733/2000000000000 : ℚ) : ℝ) ≤ stT256 250 := by
  have hc : ((694863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87893915733/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((694863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c251 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((61001/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109727/2000000) (δ := 6443/500000000) (ψ := 579807/1000000) 256 225
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t251 : ((154005970851/2500000000000 : ℚ) : ℝ) ≤ stT256 251 := by
  have hc : ((487983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154005970851/2500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((487983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c252 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((65463/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3093339/10000000) (δ := 6443/500000000) (ψ := 579807/1000000) 256 225
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t252 : ((2061573141/100000000000 : ℚ) : ℝ) ≤ stT256 252 := by
  have hc : ((65453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2061573141/100000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((65453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c253 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-125821/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1125599/2000000) (δ := 6443/500000000) (ψ := 579807/1000000) 256 225
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t253 : ((-15821864109/400000000000 : ℚ) : ℝ) ≤ stT256 253 := by
  have hc : ((-125831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15821864109/400000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-125831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c254 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-992871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236103/312500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t254 : ((-2433649371/39062500000 : ℚ) : ℝ) ≤ stT256 254 := by
  have hc : ((-992921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2433649371/39062500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-992921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c255 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-215419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157517/312500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t255 : ((-1349164189/50000000000 : ℚ) : ℝ) ≤ stT256 255 := by
  have hc : ((-53861/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1349164189/50000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-53861/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c256 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((528249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79239/312500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t256 : ((528199/16000000 : ℚ) : ℝ) ≤ stT256 256 := by
  have hc : ((528199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((528199/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((528199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c257 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((249967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1267/312500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t257 : ((155917117919/2500000000000 : ℚ) : ℝ) ≤ stT256 257 := by
  have hc : ((499909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155917117919/2500000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((499909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c258 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((558717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76403/312500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t258 : ((86952607881/2500000000000 : ℚ) : ℝ) ≤ stT256 258 := by
  have hc : ((558667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86952607881/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((558667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c259 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-387113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153773/312500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t259 : ((-24057147331/1000000000000 : ℚ) : ℝ) ≤ stT256 259 := by
  have hc : ((-387163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24057147331/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-387163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c260 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-61413/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46169/62500) (δ := 1603/125000000) (ψ := 579807/1000000) 256 226
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t260 : ((-152354735623/2500000000000 : ℚ) : ℝ) ≤ stT256 260 := by
  have hc : ((-491329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152354735623/2500000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-491329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c261 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-349801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5864091/10000000) (δ := 12931/1000000000) (ψ := 579807/1000000) 256 227
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t261 : ((-21653704661/500000000000 : ℚ) : ℝ) ≤ stT256 261 := by
  have hc : ((-174913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21653704661/500000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-174913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c262 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((40543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3416667/10000000) (δ := 38531/1000000000) (ψ := 579807/1000000) 256 227
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t262 : ((12520684233/1000000000000 : ℚ) : ℝ) ≤ stT256 262 := by
  have hc : ((40533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12520684233/1000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((40533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c263 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((924363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -978587/10000000) (δ := 12931/1000000000) (ψ := 579807/1000000) 256 227
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t263 : ((284977713969/5000000000000 : ℚ) : ℝ) ≤ stT256 263 := by
  have hc : ((924313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284977713969/5000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((924313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c264 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((418201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1450277/10000000) (δ := 38531/1000000000) (ψ := 579807/1000000) 256 227
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t264 : ((2010698019/39062500000 : ℚ) : ℝ) ≤ stT256 264 := by
  have hc : ((13068/15625 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2010698019/39062500000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((13068/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c265 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((2853/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154797/400000) (δ := 12931/1000000000) (ψ := 579807/1000000) 256 227
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t265 : ((1398995433/1000000000000 : ℚ) : ℝ) ≤ stT256 265 := by
  have hc : ((11387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1398995433/1000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((11387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c266 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-404191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1256097/2000000) (δ := 12931/1000000000) (ψ := 579807/1000000) 256 227
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t266 : ((-1549006239/31250000000 : ℚ) : ℝ) ≤ stT256 266 := by
  have hc : ((-50527/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1549006239/31250000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-50527/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c267 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-118207/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7026007/10000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t267 : ((-289381780323/5000000000000 : ℚ) : ℝ) ≤ stT256 267 := by
  have hc : ((-472853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289381780323/5000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-472853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c268 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-55771/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -926699/2000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t268 : ((-1064803509/62500000000 : ℚ) : ℝ) ≤ stT256 268 := by
  have hc : ((-55781/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1064803509/62500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-55781/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c269 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((38853/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2249879/10000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t269 : ((18949725829/500000000000 : ℚ) : ℝ) ≤ stT256 269 := by
  have hc : ((310799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18949725829/500000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((310799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c270 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((31211/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24981/2000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t270 : ((15194751579/250000000000 : ℚ) : ℝ) ≤ stT256 270 := by
  have hc : ((499351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15194751579/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((499351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c271 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((108671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2490921/10000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t271 : ((2062711763/62500000000 : ℚ) : ℝ) ≤ stT256 271 := by
  have hc : ((108661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2062711763/62500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((108661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c272 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-36019/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4848169/10000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t272 : ((-136517451/6250000000 : ℚ) : ℝ) ≤ stT256 272 := by
  have hc : ((-4503/12500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136517451/6250000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-4503/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c273 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-193129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7196777/10000000) (δ := 2593/200000000) (ψ := 579807/1000000) 256 228
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t273 : ((-29223282673/500000000000 : ℚ) : ℝ) ≤ stT256 273 := by
  have hc : ((-193139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29223282673/500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-193139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c274 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-390929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -617109/1000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t274 : ((-118092151671/2500000000000 : ℚ) : ℝ) ≤ stT256 274 := by
  have hc : ((-195477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118092151671/2500000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-195477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c275 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((4367/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1919817/5000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t275 : ((5259256373/2500000000000 : ℚ) : ℝ) ≤ stT256 275 := by
  have hc : ((17443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5259256373/2500000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((17443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c276 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((821577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -758281/5000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t276 : ((494500925583/10000000000000 : ℚ) : ℝ) ≤ stT256 276 := by
  have hc : ((821527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((494500925583/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((821527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c277 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((949471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 399063/5000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t277 : ((570451063061/10000000000000 : ℚ) : ℝ) ≤ stT256 277 := by
  have hc : ((949421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((570451063061/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((949421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c278 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((4039/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310443/1000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t278 : ((242205579/12500000000 : ℚ) : ℝ) ≤ stT256 278 := by
  have hc : ((32307/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242205579/12500000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((32307/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c279 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-278251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2701207/5000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t279 : ((-8329983353/250000000000 : ℚ) : ℝ) ≤ stT256 279 := by
  have hc : ((-69569/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8329983353/250000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-69569/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c280 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-997909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769227/1000000) (δ := 12857/1000000000) (ψ := 579807/1000000) 256 229
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t280 : ((-119279053557/2000000000000 : ℚ) : ℝ) ≤ stT256 280 := by
  have hc : ((-997959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119279053557/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-997959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c281 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-330759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5734093/10000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t281 : ((-123330747/3125000000 : ℚ) : ℝ) ≤ stT256 281 := by
  have hc : ((-10337/15625 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123330747/3125000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-10337/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c282 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((185493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3460557/10000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t282 : ((110429637513/10000000000000 : ℚ) : ℝ) ≤ stT256 282 := by
  have hc : ((185443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110429637513/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((185443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c283 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((887901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239017/2000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t283 : ((263886186369/5000000000000 : ℚ) : ℝ) ≤ stT256 283 := by
  have hc : ((887851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263886186369/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((887851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c284 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((911047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1062451/10000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t284 : ((54057650983/1000000000000 : ℚ) : ℝ) ≤ stT256 284 := by
  have hc : ((910997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54057650983/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((910997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c285 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((30441/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3311987/10000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t285 : ((18027963293/1250000000000 : ℚ) : ℝ) ≤ stT256 285 := by
  have hc : ((121739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18027963293/1250000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((121739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c286 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-121147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1110743/2000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t286 : ((-71641709141/2000000000000 : ℚ) : ℝ) ≤ stT256 286 := by
  have hc : ((-121157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71641709141/2000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-121157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c287 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-999647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7787571/10000000) (δ := 12853/1000000000) (ψ := 579807/1000000) 256 230
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t287 : ((-295051572277/5000000000000 : ℚ) : ℝ) ≤ stT256 287 := by
  have hc : ((-999697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295051572277/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-999697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c288 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-649511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711793/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t288 : ((-47844714577/1250000000000 : ℚ) : ℝ) ≤ stT256 288 := by
  have hc : ((-649561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47844714577/1250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-649561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c289 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((179429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434497/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t289 : ((21103401213/2000000000000 : ℚ) : ℝ) ≤ stT256 289 := by
  have hc : ((179379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21103401213/2000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((179379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c290 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((874647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158153/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t290 : ((25679042517/500000000000 : ℚ) : ℝ) ≤ stT256 290 := by
  have hc : ((874597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25679042517/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((874597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c291 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((930457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117231/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t291 : ((54541388747/1000000000000 : ℚ) : ℝ) ≤ stT256 291 := by
  have hc : ((930407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54541388747/1000000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((930407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c292 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((7803/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391679/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t292 : ((3652498487/200000000000 : ℚ) : ℝ) ≤ stT256 292 := by
  have hc : ((31207/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3652498487/200000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((31207/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c293 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-16541/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665183/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t293 : ((-154628492967/5000000000000 : ℚ) : ℝ) ≤ stT256 293 := by
  have hc : ((-264681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154628492967/5000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-264681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c294 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-495053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 937751/1250000) (δ := 81/6250000) (ψ := 579807/1000000) 256 231
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t294 : ((-36091928817/625000000000 : ℚ) : ℝ) ≤ stT256 294 := by
  have hc : ((-247539/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36091928817/625000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-247539/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c295 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-149237/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1508193/2500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t295 : ((-86895036081/2000000000000 : ℚ) : ℝ) ≤ stT256 295 := by
  have hc : ((-149247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86895036081/2000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-149247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c296 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((4803/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966737/2500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t296 : ((1392936867/1000000000000 : ℚ) : ℝ) ≤ stT256 296 := by
  have hc : ((4793/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1392936867/1000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((4793/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c297 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((775451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85421/500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t297 : ((224966316729/5000000000000 : ℚ) : ℝ) ≤ stT256 297 := by
  have hc : ((775401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224966316729/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((775401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c298 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((492177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110703/2500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t298 : ((8909243099/156250000000 : ℚ) : ℝ) ≤ stT256 298 := by
  have hc : ((61519/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8909243099/156250000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((61519/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c299 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((510741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646719/2500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t299 : ((147669877487/5000000000000 : ℚ) : ℝ) ≤ stT256 299 := by
  have hc : ((510691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147669877487/5000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((510691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c300 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-4896/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1180943/2500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t300 : ((-90469169647/5000000000000 : ℚ) : ℝ) ≤ stT256 300 := by
  have hc : ((-156697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90469169647/5000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-156697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c301 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-230249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1713391/2500000) (δ := 1617/125000000) (ψ := 579807/1000000) 256 232
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t301 : ((-265441312493/5000000000000 : ℚ) : ℝ) ≤ stT256 301 := by
  have hc : ((-460523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265441312493/5000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-460523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c302 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-90091/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6731647/10000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t302 : ((-810070029/15625000000 : ℚ) : ℝ) ≤ stT256 302 := by
  have hc : ((-5631/6250 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810070029/15625000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-5631/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c303 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-272103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -923187/2000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t303 : ((-31269563241/2000000000000 : ℚ) : ℝ) ≤ stT256 303 := by
  have hc : ((-272153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31269563241/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-272153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c304 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((537877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2507199/10000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t304 : ((308464759753/10000000000000 : ℚ) : ℝ) ≤ stT256 304 := by
  have hc : ((537827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308464759753/10000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((537827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c305 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((493439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405439/10000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t305 : ((70631967393/1250000000000 : ℚ) : ℝ) ≤ stT256 305 := by
  have hc : ((246707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70631967393/1250000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((246707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c306 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((390099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1689537/10000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t306 : ((111495046457/2500000000000 : ℚ) : ℝ) ≤ stT256 306 := by
  have hc : ((195037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111495046457/2500000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((195037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c307 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((1493/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3777601/10000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t307 : ((340554591/100000000000 : ℚ) : ℝ) ≤ stT256 307 := by
  have hc : ((5967/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340554591/100000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((5967/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c308 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-698111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5858881/10000000) (δ := 12829/1000000000) (ψ := 579807/1000000) 256 233
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t308 : ((-397814232283/10000000000000 : ℚ) : ℝ) ≤ stT256 308 := by
  have hc : ((-698161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397814232283/10000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-698161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c309 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-199899/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3887261/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t309 : ((-113724431829/2000000000000 : ℚ) : ℝ) ≤ stT256 309 := by
  have hc : ((-199909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113724431829/2000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-199909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c310 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-81657/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2853341/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t310 : ((-92763245593/2500000000000 : ℚ) : ℝ) ≤ stT256 310 := by
  have hc : ((-326653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92763245593/2500000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-326653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c311 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((22477/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1822717/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t311 : ((12739844949/2000000000000 : ℚ) : ℝ) ≤ stT256 311 := by
  have hc : ((22467/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12739844949/2000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((22467/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c312 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((804263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -795453/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t312 : ((227647769697/5000000000000 : ℚ) : ℝ) ≤ stT256 312 := by
  have hc : ((804213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227647769697/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((804213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c313 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((245833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228547/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t313 : ((277891717353/5000000000000 : ℚ) : ℝ) ≤ stT256 313 := by
  have hc : ((491641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277891717353/5000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((491641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c314 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((108157/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1249283/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t314 : ((15257703201/500000000000 : ℚ) : ℝ) ≤ stT256 314 := by
  have hc : ((108147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15257703201/500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((108147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c315 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-12013/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2266787/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t315 : ((-13539954547/1000000000000 : ℚ) : ℝ) ≤ stT256 315 := by
  have hc : ((-24031/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13539954547/1000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-24031/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c316 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-108679/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3281059/5000000) (δ := 6441/500000000) (ψ := 579807/1000000) 256 234
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t316 : ((-15285058819/312500000000 : ℚ) : ℝ) ≤ stT256 316 := by
  have hc : ((-434741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15285058819/312500000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-434741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c317 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-191529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1424753/2000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t317 : ((-13447378573/250000000000 : ℚ) : ℝ) ≤ stT256 317 := by
  have hc : ((-191539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13447378573/250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-191539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c318 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-91007/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5108021/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t318 : ((-51039876141/2000000000000 : ℚ) : ℝ) ≤ stT256 318 := by
  have hc : ((-91017/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51039876141/2000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-91017/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c319 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((65069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3098549/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t319 : ((9106503407/500000000000 : ℚ) : ℝ) ≤ stT256 319 := by
  have hc : ((65059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9106503407/500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((65059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c320 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((905521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095477/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t320 : ((63271597067/1250000000000 : ℚ) : ℝ) ≤ stT256 320 := by
  have hc : ((905471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63271597067/1250000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((905471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c321 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((233923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 901451/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t321 : ((52222390409/1000000000000 : ℚ) : ℝ) ≤ stT256 321 := by
  have hc : ((467821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52222390409/1000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((467821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c322 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((50279/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2892107/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t322 : ((56031795149/2500000000000 : ℚ) : ℝ) ≤ stT256 322 := by
  have hc : ((201091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56031795149/2500000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((201091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c323 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-185391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4876619/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t323 : ((-2579206091/125000000000 : ℚ) : ℝ) ≤ stT256 323 := by
  have hc : ((-23177/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2579206091/125000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-23177/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c324 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-460609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6854987/10000000) (δ := 12989/1000000000) (ψ := 579807/1000000) 256 235
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t324 : ((-31988497813/625000000000 : ℚ) : ℝ) ≤ stT256 324 := by
  have hc : ((-230317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31988497813/625000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-230317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c325 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-462589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6880753/10000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t325 : ((-128306224207/2500000000000 : ℚ) : ℝ) ≤ stT256 325 := by
  have hc : ((-231307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128306224207/2500000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-231307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c326 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-96207/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -982909/2000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t326 : ((-106582147711/5000000000000 : ℚ) : ℝ) ≤ stT256 326 := by
  have hc : ((-192439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106582147711/5000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-192439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c327 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((189657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2954353/10000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t327 : ((1638541963/78125000000 : ℚ) : ℝ) ≤ stT256 327 := by
  have hc : ((5926/15625 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1638541963/78125000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((5926/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c328 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((921043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1000113/10000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t328 : ((508532731901/10000000000000 : ℚ) : ℝ) ≤ stT256 328 := by
  have hc : ((920993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((508532731901/10000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((920993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c329 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((185789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 948111/10000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t329 : ((102423120943/2000000000000 : ℚ) : ℝ) ≤ stT256 329 := by
  have hc : ((185779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102423120943/2000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((185779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c330 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((10071/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2890447/10000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t330 : ((22172824199/1000000000000 : ℚ) : ℝ) ≤ stT256 330 := by
  have hc : ((40279/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22172824199/1000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((40279/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c331 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-176119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 965379/2000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t331 : ((-121021937/6250000000 : ℚ) : ℝ) ≤ stT256 331 := by
  have hc : ((-11009/31250 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121021937/6250000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-11009/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c332 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-905353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6757519/10000000) (δ := 12907/1000000000) (ψ := 579807/1000000) 256 236
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t332 : ((-248452542633/5000000000000 : ℚ) : ℝ) ≤ stT256 332 := by
  have hc : ((-905403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248452542633/5000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-905403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c333 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-945609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1756411/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t333 : ((-518218295023/10000000000000 : ℚ) : ℝ) ≤ stT256 333 := by
  have hc : ((-945659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518218295023/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-945659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c334 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-454531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1276651/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t334 : ((-31091976657/1250000000000 : ℚ) : ℝ) ≤ stT256 334 := by
  have hc : ((-454581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31091976657/1250000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-454581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c335 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((289297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -159663/500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t335 : ((79016206213/5000000000000 : ℚ) : ℝ) ≤ stT256 335 := by
  have hc : ((289247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79016206213/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((289247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c336 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((217663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321419/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t336 : ((29684481093/625000000000 : ℚ) : ℝ) ≤ stT256 336 := by
  have hc : ((435301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29684481093/625000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((435301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c337 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((96977/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154069/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t337 : ((6602993181/125000000000 : ℚ) : ℝ) ≤ stT256 337 := by
  have hc : ((24243/25000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6602993181/125000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((24243/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c338 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((536077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 628133/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t338 : ((36445011757/1250000000000 : ℚ) : ℝ) ≤ stT256 338 := by
  have hc : ((536027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36445011757/1250000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((536027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c339 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-189367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1100821/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t339 : ((-51438648771/5000000000000 : ℚ) : ℝ) ≤ stT256 339 := by
  have hc : ((-189417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51438648771/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-189417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c340 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-405121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1572101/2500000) (δ := 12803/1000000000) (ψ := 579807/1000000) 256 237
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t340 : ((-109860807371/2500000000000 : ℚ) : ℝ) ≤ stT256 340 := by
  have hc : ((-202573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109860807371/2500000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-202573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c341 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-248031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7540007/10000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t341 : ((-268646489197/5000000000000 : ℚ) : ℝ) ≤ stT256 341 := by
  have hc : ((-496087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268646489197/5000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-496087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c342 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-640817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1133179/2000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t342 : ((-346541780713/10000000000000 : ℚ) : ℝ) ≤ stT256 342 := by
  have hc : ((-640867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-346541780713/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-640867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c343 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((25929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3797287/10000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t343 : ((874177431/312500000000 : ℚ) : ℝ) ≤ stT256 343 := by
  have hc : ((1619/31250 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((874177431/312500000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((1619/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c344 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((715367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1934119/10000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t344 : ((385672459671/10000000000000 : ℚ) : ℝ) ≤ stT256 344 := by
  have hc : ((715317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((385672459671/10000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((715317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c345 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((499767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76327/10000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t345 : ((134525798851/2500000000000 : ℚ) : ℝ) ≤ stT256 345 := by
  have hc : ((249871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134525798851/2500000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((249871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c346 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((151619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71041/400000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t346 : ((81505453227/2000000000000 : ℚ) : ℝ) ≤ stT256 346 := by
  have hc : ((151609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81505453227/2000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((151609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c347 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((121271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724613/2000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t347 : ((16268706747/2500000000000 : ℚ) : ℝ) ≤ stT256 347 := by
  have hc : ((121221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16268706747/2500000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((121221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c348 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-577057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5464793/10000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t348 : ((-309362247099/10000000000000 : ℚ) : ℝ) ≤ stT256 348 := by
  have hc : ((-577107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309362247099/10000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-577107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c349 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-48783/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7301273/10000000) (δ := 1291/100000000) (ψ := 579807/1000000) 256 238
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t349 : ((-6528573181/125000000000 : ℚ) : ℝ) ≤ stT256 349 := by
  have hc : ((-97571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6528573181/125000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-97571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c350 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-218017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6575523/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t350 : ((-233083564857/5000000000000 : ℚ) : ℝ) ≤ stT256 350 := by
  have hc : ((-436059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233083564857/5000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-436059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c351 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-64623/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4749539/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t351 : ((-34498574713/2000000000000 : ℚ) : ℝ) ≤ stT256 351 := by
  have hc : ((-64633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34498574713/2000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-64633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c352 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((388751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2928803/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t352 : ((207178021701/10000000000000 : ℚ) : ℝ) ≤ stT256 352 := by
  have hc : ((388701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207178021701/10000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((388701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c353 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((225623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113187/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t353 : ((120080286183/2500000000000 : ℚ) : ℝ) ≤ stT256 353 := by
  have hc : ((451221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120080286183/2500000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((451221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c354 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((120169/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697309/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t354 : ((127731561297/2500000000000 : ℚ) : ℝ) ≤ stT256 354 := by
  have hc : ((480651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127731561297/2500000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((480651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c355 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((26971/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2502621/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t355 : ((3578342391/125000000000 : ℚ) : ℝ) ≤ stT256 355 := by
  have hc : ((53937/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3578342391/125000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((53937/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c356 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-74907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4302941/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t356 : ((-9928471267/1250000000000 : ℚ) : ℝ) ≤ stT256 356 := by
  have hc : ((-18733/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9928471267/1250000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-18733/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c357 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-152667/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6098141/10000000) (δ := 6493/500000000) (ψ := 579807/1000000) 256 239
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t357 : ((-80805370989/2000000000000 : ℚ) : ℝ) ≤ stT256 357 := by
  have hc : ((-152677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80805370989/2000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-152677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c358 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-499953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3909807/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t358 : ((-132123436313/2500000000000 : ℚ) : ℝ) ≤ stT256 358 := by
  have hc : ((-249989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132123436313/2500000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-249989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c359 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-746617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3017199/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t359 : ((-19703795463/500000000000 : ℚ) : ℝ) ≤ stT256 359 := by
  have hc : ((-746667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19703795463/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-746667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c360 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-5219/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -425411/1000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t360 : ((-2751712387/400000000000 : ℚ) : ℝ) ≤ stT256 360 := by
  have hc : ((-5221/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2751712387/400000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-5221/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c361 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((273707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1239407/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t361 : ((14404294183/500000000000 : ℚ) : ℝ) ≤ stT256 361 := by
  have hc : ((136841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14404294183/500000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((136841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c362 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((960123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -354191/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t362 : ((126150711981/2500000000000 : ℚ) : ℝ) ≤ stT256 362 := by
  have hc : ((960073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126150711981/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((960073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c363 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((227981/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 528561/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t363 : ((239304461631/5000000000000 : ℚ) : ℝ) ≤ stT256 363 := by
  have hc : ((455937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239304461631/5000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((455937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c364 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((107319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1408881/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t364 : ((56243843523/2500000000000 : ℚ) : ℝ) ≤ stT256 364 := by
  have hc : ((214613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56243843523/2500000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((214613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c365 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-25577/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2286801/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t365 : ((-209222387/15625000000 : ℚ) : ℝ) ≤ stT256 365 := by
  have hc : ((-12791/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209222387/15625000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-12791/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c366 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-204663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3162321/5000000) (δ := 6439/500000000) (ψ := 579807/1000000) 256 240
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t366 : ((-213971451859/5000000000000 : ℚ) : ℝ) ≤ stT256 366 := by
  have hc : ((-409351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213971451859/5000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-409351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c367 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-996239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7637081/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t367 : ((-130014718211/2500000000000 : ℚ) : ℝ) ≤ stT256 367 := by
  have hc : ((-996289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130014718211/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-996289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c368 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-141709/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5895577/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t368 : ((-73876272353/2000000000000 : ℚ) : ℝ) ≤ stT256 368 := by
  have hc : ((-141719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73876272353/2000000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-141719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c369 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-46297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4158809/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t369 : ((-602857669/125000000000 : ℚ) : ℝ) ≤ stT256 369 := by
  have hc : ((-23161/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-602857669/125000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-23161/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c370 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((282367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2426713/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t370 : ((587130189/20000000000 : ℚ) : ℝ) ≤ stT256 370 := by
  have hc : ((141171/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((587130189/20000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((141171/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c371 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((961127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -699353/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t371 : ((249483095199/5000000000000 : ℚ) : ℝ) ≤ stT256 371 := by
  have hc : ((961077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249483095199/5000000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((961077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c372 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((14334/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1023399/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t372 : ((9512211957/200000000000 : ℚ) : ℝ) ≤ stT256 372 := by
  have hc : ((458663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9512211957/200000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((458663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c373 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((14269/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2741543/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t373 : ((5909915031/250000000000 : ℚ) : ℝ) ≤ stT256 373 := by
  have hc : ((228279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5909915031/250000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((228279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c374 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-209643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 891003/2000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t374 : ((-3388429187/312500000000 : ℚ) : ℝ) ≤ stT256 374 := by
  have hc : ((-209693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3388429187/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-209693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c375 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-97511/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6164007/10000000) (δ := 401/31250000) (ψ := 579807/1000000) 256 241
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t375 : ((-100715425731/2500000000000 : ℚ) : ℝ) ≤ stT256 375 := by
  have hc : ((-390069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100715425731/2500000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-390069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c376 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-999983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1959893/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t376 : ((-515728018463/10000000000000 : ℚ) : ℝ) ≤ stT256 376 := by
  have hc : ((-1000033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515728018463/10000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-1000033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c377 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-96747/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1534933/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t377 : ((-199322144351/5000000000000 : ℚ) : ℝ) ≤ stT256 377 := by
  have hc : ((-387013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199322144351/5000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-387013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c378 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-102739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1111093/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t378 : ((-2642807479/250000000000 : ℚ) : ℝ) ≤ stT256 378 := by
  have hc : ((-25691/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2642807479/250000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-25691/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c379 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((226187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -688357/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t379 : ((11617150373/500000000000 : ℚ) : ℝ) ≤ stT256 379 := by
  have hc : ((113081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11617150373/500000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((113081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c380 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((91029/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266757/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t380 : ((2918394421/62500000000 : ℚ) : ℝ) ≤ stT256 380 := by
  have hc : ((5689/6250 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2918394421/62500000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((5689/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c381 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((969899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153739/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t381 : ((99373638087/2000000000000 : ℚ) : ℝ) ≤ stT256 381 := by
  have hc : ((969849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99373638087/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((969849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c382 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((38011/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 573147/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t382 : ((38893002393/1250000000000 : ℚ) : ℝ) ≤ stT256 382 := by
  have hc : ((304063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38893002393/1250000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((304063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c383 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-15499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198287/500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t383 : ((-7945181373/10000000000000 : ℚ) : ℝ) ≤ stT256 383 := by
  have hc : ((-15549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7945181373/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-15549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c384 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-315579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1408651/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t384 : ((-40264048211/1250000000000 : ℚ) : ℝ) ≤ stT256 384 := by
  have hc : ((-78901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40264048211/1250000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-78901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c385 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-975471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1824779/2500000) (δ := 12939/1000000000) (ψ := 579807/1000000) 256 242
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t385 : ((-31073270413/625000000000 : ℚ) : ℝ) ≤ stT256 385 := by
  have hc : ((-975521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31073270413/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-975521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c386 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-112981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421793/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t386 : ((-230036165663/5000000000000 : ℚ) : ℝ) ≤ stT256 386 := by
  have hc : ((-451949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230036165663/5000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-451949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c387 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-449611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -318301/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t387 : ((-228575726469/10000000000000 : ℚ) : ℝ) ≤ stT256 387 := by
  have hc : ((-449661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228575726469/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-449661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c388 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((48277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215073/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t388 : ((49005167017/5000000000000 : ℚ) : ℝ) ≤ stT256 388 := by
  have hc : ((96529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49005167017/5000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((96529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c389 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((753437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112113/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t389 : ((19099113837/500000000000 : ℚ) : ℝ) ≤ stT256 389 := by
  have hc : ((753387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19099113837/500000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((753387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c390 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((124773/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9417/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t390 : ((252712057723/5000000000000 : ℚ) : ℝ) ≤ stT256 390 := by
  have hc : ((499067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252712057723/5000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((499067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c391 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((827983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18603/125000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t391 : ((418703104693/10000000000000 : ℚ) : ℝ) ≤ stT256 391 := by
  have hc : ((827933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418703104693/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((827933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c392 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((79021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195187/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t392 : ((19952648573/1250000000000 : ℚ) : ℝ) ≤ stT256 392 := by
  have hc : ((158017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19952648573/1250000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((158017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c393 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-162323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297099/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t393 : ((-10236731379/625000000000 : ℚ) : ℝ) ≤ stT256 393 := by
  have hc : ((-40587/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10236731379/625000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-40587/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c394 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-831171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398751/625000) (δ := 12957/1000000000) (ψ := 579807/1000000) 256 243
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t394 : ((-418763321253/10000000000000 : ℚ) : ℝ) ≤ stT256 394 := by
  have hc : ((-831221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418763321253/10000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-831221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c395 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-998241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -308227/400000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t395 : ((-100459021621/2000000000000 : ℚ) : ℝ) ≤ stT256 395 := by
  have hc : ((-998291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100459021621/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-998291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c396 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-380281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217487/2000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t396 : ((-95555495407/2500000000000 : ℚ) : ℝ) ≤ stT256 396 := by
  have hc : ((-190153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95555495407/2500000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-190153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c397 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-21681/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -894671/2000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t397 : ((-2720974949/250000000000 : ℚ) : ℝ) ≤ stT256 397 := by
  have hc : ((-10843/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2720974949/250000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-10843/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c398 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((16511/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2863243/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t398 : ((4137601143/200000000000 : ℚ) : ℝ) ≤ stT256 398 := by
  have hc : ((16509/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4137601143/200000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((16509/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c399 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((876193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257227/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t399 : ((219309982759/5000000000000 : ℚ) : ℝ) ≤ stT256 399 := by
  have hc : ((876143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219309982759/5000000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((876143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c400 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((495253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344757/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t400 : ((123807/2500000 : ℚ) : ℝ) ≤ stT256 400 := by
  have hc : ((123807/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123807/2500000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((123807/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c401 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((44559/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1942773/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t401 : ((11125067317/312500000000 : ℚ) : ℝ) ≤ stT256 401 := by
  have hc : ((356447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11125067317/312500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((356447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c402 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((7773/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3536757/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t402 : ((3875567957/500000000000 : ℚ) : ℝ) ≤ stT256 402 := by
  have hc : ((15541/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3875567957/500000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((15541/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c403 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-18469/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5126837/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t403 : ((-1150133757/50000000000 : ℚ) : ℝ) ≤ stT256 403 := by
  have hc : ((-18471/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1150133757/50000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-18471/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c404 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-897639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6712949/10000000) (δ := 257/20000000) (ψ := 579807/1000000) 256 244
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t404 : ((-446617333591/10000000000000 : ℚ) : ℝ) ≤ stT256 404 := by
  have hc : ((-897689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446617333591/10000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-897689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c405 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-984469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3706403/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t405 : ((-61151428647/1250000000000 : ℚ) : ℝ) ≤ stT256 405 := by
  have hc : ((-984519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61151428647/1250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-984519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c406 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-86387/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2917251/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t406 : ((-42876278829/1250000000000 : ℚ) : ℝ) ≤ stT256 406 := by
  have hc : ((-345573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42876278829/1250000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-345573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c407 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-132851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2130051/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t407 : ((-32938316741/5000000000000 : ℚ) : ℝ) ≤ stT256 407 := by
  have hc : ((-132901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32938316741/5000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-132901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c408 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((237507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1344771/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t408 : ((58785463093/2500000000000 : ℚ) : ℝ) ≤ stT256 408 := by
  have hc : ((118741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58785463093/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((118741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c409 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((450413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -561411/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t409 : ((13918903349/312500000000 : ℚ) : ℝ) ≤ stT256 409 := by
  have hc : ((112597/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13918903349/312500000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((112597/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c410 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((246137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220029/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t410 : ((30388007517/625000000000 : ℚ) : ℝ) ≤ stT256 410 := by
  have hc : ((492249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30388007517/625000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((492249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c411 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((696947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 999581/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t411 : ((343753504911/10000000000000 : ℚ) : ℝ) ≤ stT256 411 := by
  have hc : ((696897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((343753504911/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((696897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c412 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((5939/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1777213/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t412 : ((365618271/50000000000 : ℚ) : ℝ) ≤ stT256 412 := by
  have hc : ((5937/40000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365618271/50000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((5937/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c413 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-90857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2552957/5000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t413 : ((-11178185739/500000000000 : ℚ) : ℝ) ≤ stT256 413 := by
  have hc : ((-90867/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11178185739/500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-90867/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c414 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-886941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665369/1000000) (δ := 643/50000000) (ψ := 579807/1000000) 256 245
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t414 : ((-217966507367/5000000000000 : ℚ) : ℝ) ≤ stT256 414 := by
  have hc : ((-886991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217966507367/5000000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-886991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c415 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-990561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7510209/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t415 : ((-486272118291/10000000000000 : ℚ) : ℝ) ≤ stT256 415 := by
  have hc : ((-990611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-486272118291/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-990611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c416 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-364607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5969921/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t416 : ((-22346973489/625000000000 : ℚ) : ℝ) ≤ stT256 416 := by
  have hc : ((-45579/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22346973489/625000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-45579/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c417 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-40227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4433281/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t417 : ((-19704179611/2000000000000 : ℚ) : ℝ) ≤ stT256 417 := by
  have hc : ((-40237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19704179611/2000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-40237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c418 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((39921/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2900353/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t418 : ((976175717/50000000000 : ℚ) : ℝ) ≤ stT256 418 := by
  have hc : ((9979/25000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((976175717/50000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((9979/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c419 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((170669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1371073/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t419 : ((83372211929/2000000000000 : ℚ) : ℝ) ≤ stT256 419 := by
  have hc : ((170659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83372211929/2000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((170659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c420 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((99809/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154559/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t420 : ((243496809/5000000000 : ℚ) : ℝ) ≤ stT256 420 := by
  have hc : ((24951/25000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243496809/5000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((24951/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c421 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((391719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1676543/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t421 : ((9544995239/250000000000 : ℚ) : ℝ) ≤ stT256 421 := by
  have hc : ((195847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9544995239/250000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((195847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c422 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((72163/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3194943/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t422 : ((8780571549/625000000000 : ℚ) : ℝ) ≤ stT256 422 := by
  have hc : ((144301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8780571549/625000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((144301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c423 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-38499/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941939/2000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t423 : ((-74887628557/5000000000000 : ℚ) : ℝ) ≤ stT256 423 := by
  have hc : ((-154021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74887628557/5000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-154021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c424 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-79413/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6220927/10000000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t424 : ((-19284397887/500000000000 : ℚ) : ℝ) ≤ stT256 424 := by
  have hc : ((-39709/50000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19284397887/500000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-39709/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c425 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-499371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309143/400000) (δ := 1621/125000000) (ψ := 579807/1000000) 256 246
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t425 : ((-3785047133/78125000000 : ℚ) : ℝ) ≤ stT256 425 := by
  have hc : ((-124849/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3785047133/78125000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-124849/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c426 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-425873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6475261/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t426 : ((-51587108199/1250000000000 : ℚ) : ℝ) ≤ stT256 426 := by
  have hc : ((-212949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51587108199/1250000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-212949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c427 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-203453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4974653/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t427 : ((-24617480613/1250000000000 : ℚ) : ℝ) ≤ stT256 427 := by
  have hc : ((-101739/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24617480613/1250000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-101739/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c428 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((89389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3477629/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t428 : ((1349865561/156250000000 : ℚ) : ℝ) ≤ stT256 428 := by
  have hc : ((22341/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1349865561/156250000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((22341/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c429 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((175321/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1983997/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t429 : ((42319822517/1250000000000 : ℚ) : ℝ) ≤ stT256 429 := by
  have hc : ((350617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42319822517/1250000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((350617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c430 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((19611/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98777/2000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t430 : ((472838281/10000000000 : ℚ) : ℝ) ≤ stT256 430 := by
  have hc : ((1961/2000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472838281/10000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((1961/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c431 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((922193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 992707/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t431 : ((444180606669/10000000000000 : ℚ) : ℝ) ≤ stT256 431 := by
  have hc : ((922143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((444180606669/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((922143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c432 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((548387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2475907/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t432 : ((2110549113/80000000000 : ℚ) : ℝ) ≤ stT256 432 := by
  have hc : ((548337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2110549113/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((548337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c433 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-11489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 791143/2000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t433 : ((-554529723/1000000000000 : ℚ) : ℝ) ≤ stT256 433 := by
  have hc : ((-11539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554529723/1000000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-11539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c434 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-566317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5432067/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t434 : ((-16991576367/625000000000 : ℚ) : ℝ) ≤ stT256 434 := by
  have hc : ((-566367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16991576367/625000000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-566367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c435 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-46441/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6905027/10000000) (δ := 101/7812500) (ψ := 579807/1000000) 256 247
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t435 : ((-5566996571/125000000000 : ℚ) : ℝ) ≤ stT256 435 := by
  have hc : ((-92887/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5566996571/125000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-92887/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c436 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-195679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -916671/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t436 : ((-46859100873/1000000000000 : ℚ) : ℝ) ≤ stT256 436 := by
  have hc : ((-195689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46859100873/1000000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-195689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c437 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-87561/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -733399/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t437 : ((-33511286037/1000000000000 : ℚ) : ℝ) ≤ stT256 437 := by
  have hc : ((-350269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33511286037/1000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-350269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c438 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-94879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110107/250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t438 : ((-5668366797/625000000000 : ℚ) : ℝ) ≤ stT256 438 := by
  have hc : ((-11863/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5668366797/625000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-11863/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c439 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((191431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73619/250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t439 : ((45676457919/2500000000000 : ℚ) : ℝ) ≤ stT256 439 := by
  have hc : ((95703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45676457919/2500000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((95703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c440 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((827909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186071/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t440 : ((394666048929/10000000000000 : ℚ) : ℝ) ≤ stT256 440 := by
  have hc : ((827859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394666048929/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((827859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c441 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((499949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4463/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t441 : ((5951470239/125000000000 : ℚ) : ℝ) ≤ stT256 441 := by
  have hc : ((124981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5951470239/125000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((124981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c442 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((844289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176737/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t442 : ((401563124589/10000000000000 : ℚ) : ℝ) ≤ stT256 442 := by
  have hc : ((844239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401563124589/10000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((844239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c443 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((25867/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357529/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t443 : ((49153156427/2500000000000 : ℚ) : ℝ) ≤ stT256 443 := by
  have hc : ((206911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49153156427/2500000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((206911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c444 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-149957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 537913/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t444 : ((-71190172053/10000000000000 : ℚ) : ℝ) ≤ stT256 444 := by
  have hc : ((-150007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71190172053/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-150007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c445 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-664219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717889/1250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t445 : ((-157447031187/5000000000000 : ℚ) : ℝ) ≤ stT256 445 := by
  have hc : ((-664269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157447031187/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-664269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c446 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-19277/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179493/250000) (δ := 12821/1000000000) (ψ := 579807/1000000) 256 248
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t446 : ((-2282100723/50000000000 : ℚ) : ℝ) ≤ stT256 446 := by
  have hc : ((-9639/10000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2282100723/50000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-9639/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c447 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-954257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7094899/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t447 : ((-56421492761/1250000000000 : ℚ) : ℝ) ≤ stT256 447 := by
  have hc : ((-954307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56421492761/1250000000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-954307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c448 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-640447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5664691/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t448 : ((-37825831329/1250000000000 : ℚ) : ℝ) ≤ stT256 448 := by
  have hc : ((-640497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37825831329/1250000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-640497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c449 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-123983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4237747/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t449 : ((-5853489369/1000000000000 : ℚ) : ℝ) ≤ stT256 449 := by
  have hc : ((-124033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5853489369/1000000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-124033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c450 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((430657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2813939/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t450 : ((50747465557/2500000000000 : ℚ) : ℝ) ≤ stT256 450 := by
  have hc : ((430607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50747465557/2500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((430607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c451 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((848683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1393267/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t451 : ((399605155673/10000000000000 : ℚ) : ℝ) ≤ stT256 451 := by
  have hc : ((848633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399605155673/10000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((848633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c452 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((999953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4841/2000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t452 : ((11757859377/250000000000 : ℚ) : ℝ) ≤ stT256 452 := by
  have hc : ((999903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11757859377/250000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((999903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c453 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((104869/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287721/2000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t453 : ((2463435723/62500000000 : ℚ) : ℝ) ≤ stT256 453 := by
  have hc : ((419451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2463435723/62500000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((419451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c454 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((83533/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 569961/2000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t454 : ((39199264929/2000000000000 : ℚ) : ℝ) ≤ stT256 454 := by
  have hc : ((83523/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39199264929/2000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((83523/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c455 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-8251/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4257997/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t455 : ((-3869599833/625000000000 : ℚ) : ℝ) ≤ stT256 455 := by
  have hc : ((-66033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3869599833/625000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-66033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c456 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-79993/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5663053/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t456 : ((-149852355121/5000000000000 : ℚ) : ℝ) ≤ stT256 456 := by
  have hc : ((-319997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149852355121/5000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-319997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c457 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-950609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7064973/10000000) (δ := 12889/1000000000) (ψ := 579807/1000000) 256 249
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t457 : ((-444700217679/10000000000000 : ℚ) : ℝ) ≤ stT256 457 := by
  have hc : ((-950659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444700217679/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-950659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c458 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-970389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3622039/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t458 : ((-45345703153/1000000000000 : ℚ) : ℝ) ≤ stT256 458 := by
  have hc : ((-970439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45345703153/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-970439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c459 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-347519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2924087/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t459 : ((-20277498123/625000000000 : ℚ) : ℝ) ≤ stT256 459 := by
  have hc : ((-43443/62500 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20277498123/625000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-43443/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c460 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-52449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2227703/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t460 : ((-48920663519/5000000000000 : ℚ) : ℝ) ≤ stT256 460 := by
  have hc : ((-104923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48920663519/5000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-104923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c461 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((168893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1532791/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t461 : ((9831199441/625000000000 : ℚ) : ℝ) ≤ stT256 461 := by
  have hc : ((42217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9831199441/625000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((42217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c462 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((782869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167883/1000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t462 : ((182100138599/5000000000000 : ℚ) : ℝ) ≤ stT256 462 := by
  have hc : ((782819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182100138599/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((782819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c463 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((198609/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -147511/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t463 : ((92296700661/2000000000000 : ℚ) : ℝ) ≤ stT256 463 := by
  have hc : ((198599/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92296700661/2000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((198599/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c464 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((22679/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 542889/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t464 : ((21055746609/500000000000 : ℚ) : ℝ) ≤ stT256 464 := by
  have hc : ((90711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21055746609/500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((90711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c465 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((110497/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1231817/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t465 : ((25618510203/1000000000000 : ℚ) : ℝ) ≤ stT256 465 := by
  have hc : ((110487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25618510203/1000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((110487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c466 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((8849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1919241/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t466 : ((8186858193/5000000000000 : ℚ) : ℝ) ≤ stT256 466 := by
  have hc : ((17673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8186858193/5000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((17673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c467 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-98221/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2605193/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t467 : ((-9091180819/400000000000 : ℚ) : ℝ) ≤ stT256 467 := by
  have hc : ((-98231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9091180819/400000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-98231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c468 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-54551/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3289673/5000000) (δ := 3249/250000000) (ψ := 579807/1000000) 256 250
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t468 : ((-201741590683/5000000000000 : ℚ) : ℝ) ≤ stT256 468 := by
  have hc : ((-436433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201741590683/5000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-436433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c469 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-999331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3881269/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t469 : ((-230736085899/5000000000000 : ℚ) : ℝ) ≤ stT256 469 := by
  have hc : ((-999381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230736085899/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-999381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c470 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-835457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3199701/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t470 : ((-192695485931/5000000000000 : ℚ) : ℝ) ≤ stT256 470 := by
  have hc : ((-835507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192695485931/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-835507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c471 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-430333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2519573/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t471 : ((-24788769651/1250000000000 : ℚ) : ℝ) ≤ stT256 471 := by
  have hc : ((-430383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24788769651/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-430383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c472 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((97931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368177/1000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t472 : ((45053351847/10000000000000 : ℚ) : ℝ) ≤ stT256 472 := by
  have hc : ((97881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45053351847/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((97881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c473 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((119421/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1163637/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t473 : ((274525889/10000000000 : ℚ) : ℝ) ≤ stT256 473 := by
  have hc : ((119411/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274525889/10000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((119411/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c474 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((924819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -487797/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t474 : ((84952054647/2000000000000 : ℚ) : ℝ) ≤ stT256 474 := by
  have hc : ((924769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84952054647/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((924769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c475 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((494439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186603/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t475 : ((113426235017/2500000000000 : ℚ) : ℝ) ≤ stT256 475 := by
  have hc : ((247207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113426235017/2500000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((247207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c476 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((772739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 859563/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t476 : ((354161230461/10000000000000 : ℚ) : ℝ) ≤ stT256 476 := by
  have hc : ((772689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354161230461/10000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((772689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c477 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((42381/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 306223/1000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t477 : ((19402042033/1250000000000 : ℚ) : ℝ) ≤ stT256 477 := by
  have hc : ((169499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19402042033/1250000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((169499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c478 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-189091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2201291/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t478 : ((-8651120199/1000000000000 : ℚ) : ℝ) ≤ stT256 478 := by
  have hc : ((-189141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8651120199/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-189141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c479 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-82913/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2870027/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t479 : ((-9471700089/312500000000 : ℚ) : ℝ) ≤ stT256 479 := by
  have hc : ((-331677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9471700089/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-331677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c480 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-951827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3537419/5000000) (δ := 12899/1000000000) (ψ := 579807/1000000) 256 251
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t480 : ((-108617732593/2500000000000 : ℚ) : ℝ) ≤ stT256 480 := by
  have hc : ((-951877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108617732593/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-951877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c481 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-121957/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7301221/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t481 : ((-222441941733/5000000000000 : ℚ) : ℝ) ≤ stT256 481 := by
  have hc : ((-487853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222441941733/5000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-487853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c482 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-91223/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1194401/2000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t482 : ((-2597114289/78125000000 : ℚ) : ℝ) ≤ stT256 482 := by
  have hc : ((-364917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2597114289/78125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-364917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c483 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-17719/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -929121/2000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t483 : ((-8063850429/625000000000 : ℚ) : ℝ) ≤ stT256 483 := by
  have hc : ((-141777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8063850429/625000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-141777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c484 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((239683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3321893/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t484 : ((21784796397/2000000000000 : ℚ) : ℝ) ≤ stT256 484 := by
  have hc : ((239633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21784796397/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((239633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c485 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((696421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2000997/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t485 : ((79051339549/2500000000000 : ℚ) : ℝ) ≤ stT256 485 := by
  have hc : ((696371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79051339549/2500000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((696371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c486 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((481471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27309/400000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t486 : ((109194119307/2500000000000 : ℚ) : ℝ) ≤ stT256 486 := by
  have hc : ((240723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109194119307/2500000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((240723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c487 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((121017/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126559/2000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t487 : ((219340697149/5000000000000 : ℚ) : ℝ) ≤ stT256 487 := by
  have hc : ((484043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219340697149/5000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((484043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c488 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((712143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1945627/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t488 : ((161174417527/5000000000000 : ℚ) : ℝ) ≤ stT256 488 := by
  have hc : ((712093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161174417527/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((712093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c489 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((265299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3255707/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t489 : ((23989915307/2000000000000 : ℚ) : ℝ) ≤ stT256 489 := by
  have hc : ((265249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23989915307/2000000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((265249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c490 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-251731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4563163/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t490 : ((-56871536937/5000000000000 : ℚ) : ℝ) ≤ stT256 490 := by
  have hc : ((-251781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56871536937/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-251781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c491 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-700717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1173599/2000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t491 : ((-158125971249/5000000000000 : ℚ) : ℝ) ≤ stT256 491 := by
  have hc : ((-700767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158125971249/5000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-700767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c492 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-962821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7170139/10000000) (δ := 12811/1000000000) (ψ := 579807/1000000) 256 252
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t492 : ((-86819189457/2000000000000 : ℚ) : ℝ) ≤ stT256 492 := by
  have hc : ((-962871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86819189457/2000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-962871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c493 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-484917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226199/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t493 : ((-54601802019/1250000000000 : ℚ) : ℝ) ≤ stT256 493 := by
  have hc : ((-242471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54601802019/1250000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-242471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c494 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-36069/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185671/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t494 : ((-16229361423/500000000000 : ℚ) : ℝ) ≤ stT256 494 := by
  have hc : ((-72143/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16229361423/500000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-72143/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c495 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((-14207/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145227/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t495 : ((-12773402673/1000000000000 : ℚ) : ℝ) ≤ stT256 495 := by
  have hc : ((-28419/100000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12773402673/1000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-28419/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c496 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((45313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104863/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t496 : ((20341635939/2000000000000 : ℚ) : ℝ) ≤ stT256 496 := by
  have hc : ((45303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20341635939/2000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((45303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c497 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((338677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64581/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t497 : ((37976519943/1250000000000 : ℚ) : ℝ) ≤ stT256 497 := by
  have hc : ((84663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37976519943/1250000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((84663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c498 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((475849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24381/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t498 : ((1332634329/31250000000 : ℚ) : ℝ) ≤ stT256 498 := by
  have hc : ((29739/31250 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1332634329/31250000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((29739/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c499 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((15309/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15739/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t499 : ((219292560443/5000000000000 : ℚ) : ℝ) ≤ stT256 499 := by
  have hc : ((489863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219292560443/5000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((489863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_c500 :
    |Real.cos (((256 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((755767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55779/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st256_t500 : ((337966466721/10000000000000 : ℚ) : ℝ) ≤ stT256 500 := by
  have hc : ((755717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((256 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st256_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337966466721/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((755717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st256_p1 : ((418259/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT256 (i+1) := by
  rw [Finset.sum_range_one]
  exact st256_t1

theorem st256_p2 : ((627711075607/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT256 (i+1))
      = (∑ i ∈ Finset.range 1, stT256 (i+1)) + stT256 2 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 1
    simpa using h
  have hprev := st256_p1
  have hstep := st256_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p3 : ((9747473443211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT256 (i+1))
      = (∑ i ∈ Finset.range 2, stT256 (i+1)) + stT256 3 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 2
    simpa using h
  have hprev := st256_p2
  have hstep := st256_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p4 : ((22992100277/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT256 (i+1))
      = (∑ i ∈ Finset.range 3, stT256 (i+1)) + stT256 4 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 3
    simpa using h
  have hprev := st256_p3
  have hstep := st256_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p5 : ((45056295787/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT256 (i+1))
      = (∑ i ∈ Finset.range 4, stT256 (i+1)) + stT256 5 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 4
    simpa using h
  have hprev := st256_p4
  have hstep := st256_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p6 : ((1224085144709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT256 (i+1))
      = (∑ i ∈ Finset.range 5, stT256 (i+1)) + stT256 6 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 5
    simpa using h
  have hprev := st256_p5
  have hstep := st256_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p7 : ((39126666827/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT256 (i+1))
      = (∑ i ∈ Finset.range 6, stT256 (i+1)) + stT256 7 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 6
    simpa using h
  have hprev := st256_p6
  have hstep := st256_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p8 : ((483626917811/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT256 (i+1))
      = (∑ i ∈ Finset.range 7, stT256 (i+1)) + stT256 8 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 7
    simpa using h
  have hprev := st256_p7
  have hstep := st256_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p9 : ((52907587791/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT256 (i+1))
      = (∑ i ∈ Finset.range 8, stT256 (i+1)) + stT256 9 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 8
    simpa using h
  have hprev := st256_p8
  have hstep := st256_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p10 : ((20111602653/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT256 (i+1))
      = (∑ i ∈ Finset.range 9, stT256 (i+1)) + stT256 10 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 9
    simpa using h
  have hprev := st256_p9
  have hstep := st256_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p11 : ((-1020080598309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT256 (i+1))
      = (∑ i ∈ Finset.range 10, stT256 (i+1)) + stT256 11 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 10
    simpa using h
  have hprev := st256_p10
  have hstep := st256_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p12 : ((-46487752527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT256 (i+1))
      = (∑ i ∈ Finset.range 11, stT256 (i+1)) + stT256 12 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 11
    simpa using h
  have hprev := st256_p11
  have hstep := st256_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p13 : ((-1371409128031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT256 (i+1))
      = (∑ i ∈ Finset.range 12, stT256 (i+1)) + stT256 13 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 12
    simpa using h
  have hprev := st256_p12
  have hstep := st256_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p14 : ((-5179404784193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT256 (i+1))
      = (∑ i ∈ Finset.range 13, stT256 (i+1)) + stT256 14 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 13
    simpa using h
  have hprev := st256_p13
  have hstep := st256_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p15 : ((-5075965180937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT256 (i+1))
      = (∑ i ∈ Finset.range 14, stT256 (i+1)) + stT256 15 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 14
    simpa using h
  have hprev := st256_p14
  have hstep := st256_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p16 : ((-3329000180937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT256 (i+1))
      = (∑ i ∈ Finset.range 15, stT256 (i+1)) + stT256 16 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 15
    simpa using h
  have hprev := st256_p15
  have hstep := st256_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p17 : ((-4669824843389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT256 (i+1))
      = (∑ i ∈ Finset.range 16, stT256 (i+1)) + stT256 17 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 16
    simpa using h
  have hprev := st256_p16
  have hstep := st256_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p18 : ((-2889306623013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT256 (i+1))
      = (∑ i ∈ Finset.range 17, stT256 (i+1)) + stT256 18 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 17
    simpa using h
  have hprev := st256_p17
  have hstep := st256_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p19 : ((-831391709307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT256 (i+1))
      = (∑ i ∈ Finset.range 18, stT256 (i+1)) + stT256 19 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 18
    simpa using h
  have hprev := st256_p18
  have hstep := st256_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p20 : ((-1975366610789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT256 (i+1))
      = (∑ i ∈ Finset.range 19, stT256 (i+1)) + stT256 20 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 19
    simpa using h
  have hprev := st256_p19
  have hstep := st256_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p21 : ((22228068267/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT256 (i+1))
      = (∑ i ∈ Finset.range 20, stT256 (i+1)) + stT256 21 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 20
    simpa using h
  have hprev := st256_p20
  have hstep := st256_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p22 : ((268747773663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT256 (i+1))
      = (∑ i ∈ Finset.range 21, stT256 (i+1)) + stT256 22 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 21
    simpa using h
  have hprev := st256_p21
  have hstep := st256_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p23 : ((8722766791/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT256 (i+1))
      = (∑ i ∈ Finset.range 22, stT256 (i+1)) + stT256 23 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 22
    simpa using h
  have hprev := st256_p22
  have hstep := st256_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p24 : ((-1381343958083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT256 (i+1))
      = (∑ i ∈ Finset.range 23, stT256 (i+1)) + stT256 24 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 23
    simpa using h
  have hprev := st256_p23
  have hstep := st256_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p25 : ((493754041917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT256 (i+1))
      = (∑ i ∈ Finset.range 24, stT256 (i+1)) + stT256 25 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 24
    simpa using h
  have hprev := st256_p24
  have hstep := st256_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p26 : ((-613602353249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT256 (i+1))
      = (∑ i ∈ Finset.range 25, stT256 (i+1)) + stT256 26 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 25
    simpa using h
  have hprev := st256_p25
  have hstep := st256_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p27 : ((70014687751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT256 (i+1))
      = (∑ i ∈ Finset.range 26, stT256 (i+1)) + stT256 27 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 26
    simpa using h
  have hprev := st256_p26
  have hstep := st256_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p28 : ((-399575408293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT256 (i+1))
      = (∑ i ∈ Finset.range 27, stT256 (i+1)) + stT256 28 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 27
    simpa using h
  have hprev := st256_p27
  have hstep := st256_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p29 : ((677310656761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT256 (i+1))
      = (∑ i ∈ Finset.range 28, stT256 (i+1)) + stT256 29 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 28
    simpa using h
  have hprev := st256_p28
  have hstep := st256_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p30 : ((-228077059649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT256 (i+1))
      = (∑ i ∈ Finset.range 29, stT256 (i+1)) + stT256 30 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 29
    simpa using h
  have hprev := st256_p29
  have hstep := st256_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p31 : ((-366081705203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT256 (i+1))
      = (∑ i ∈ Finset.range 30, stT256 (i+1)) + stT256 31 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 30
    simpa using h
  have hprev := st256_p30
  have hstep := st256_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p32 : ((963465709993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT256 (i+1))
      = (∑ i ∈ Finset.range 31, stT256 (i+1)) + stT256 32 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 31
    simpa using h
  have hprev := st256_p31
  have hstep := st256_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p33 : ((-214277858681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT256 (i+1))
      = (∑ i ∈ Finset.range 32, stT256 (i+1)) + stT256 33 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 32
    simpa using h
  have hprev := st256_p32
  have hstep := st256_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p34 : ((-1692847893623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT256 (i+1))
      = (∑ i ∈ Finset.range 33, stT256 (i+1)) + stT256 34 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 33
    simpa using h
  have hprev := st256_p33
  have hstep := st256_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p35 : ((-1527175735619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT256 (i+1))
      = (∑ i ∈ Finset.range 34, stT256 (i+1)) + stT256 35 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 34
    simpa using h
  have hprev := st256_p34
  have hstep := st256_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p36 : ((-101192972679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT256 (i+1))
      = (∑ i ∈ Finset.range 35, stT256 (i+1)) + stT256 36 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 35
    simpa using h
  have hprev := st256_p35
  have hstep := st256_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p37 : ((302813792707/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT256 (i+1))
      = (∑ i ∈ Finset.range 36, stT256 (i+1)) + stT256 37 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 36
    simpa using h
  have hprev := st256_p36
  have hstep := st256_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p38 : ((2721930574799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT256 (i+1))
      = (∑ i ∈ Finset.range 37, stT256 (i+1)) + stT256 38 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 37
    simpa using h
  have hprev := st256_p37
  have hstep := st256_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p39 : ((862985843433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT256 (i+1))
      = (∑ i ∈ Finset.range 38, stT256 (i+1)) + stT256 39 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 38
    simpa using h
  have hprev := st256_p38
  have hstep := st256_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p40 : ((1940806440909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT256 (i+1))
      = (∑ i ∈ Finset.range 39, stT256 (i+1)) + stT256 40 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 39
    simpa using h
  have hprev := st256_p39
  have hstep := st256_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p41 : ((1062106074489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT256 (i+1))
      = (∑ i ∈ Finset.range 40, stT256 (i+1)) + stT256 41 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 40
    simpa using h
  have hprev := st256_p40
  have hstep := st256_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p42 : ((2389695605727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT256 (i+1))
      = (∑ i ∈ Finset.range 41, stT256 (i+1)) + stT256 42 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 41
    simpa using h
  have hprev := st256_p41
  have hstep := st256_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p43 : ((5653825235379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT256 (i+1))
      = (∑ i ∈ Finset.range 42, stT256 (i+1)) + stT256 43 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 42
    simpa using h
  have hprev := st256_p42
  have hstep := st256_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p44 : ((1385852869123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT256 (i+1))
      = (∑ i ∈ Finset.range 43, stT256 (i+1)) + stT256 44 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 43
    simpa using h
  have hprev := st256_p43
  have hstep := st256_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p45 : ((8419134584611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT256 (i+1))
      = (∑ i ∈ Finset.range 44, stT256 (i+1)) + stT256 45 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 44
    simpa using h
  have hprev := st256_p44
  have hstep := st256_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p46 : ((9615165584383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT256 (i+1))
      = (∑ i ∈ Finset.range 45, stT256 (i+1)) + stT256 46 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 45
    simpa using h
  have hprev := st256_p45
  have hstep := st256_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p47 : ((2464998131447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT256 (i+1))
      = (∑ i ∈ Finset.range 46, stT256 (i+1)) + stT256 47 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 46
    simpa using h
  have hprev := st256_p46
  have hstep := st256_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p48 : ((2225740156403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT256 (i+1))
      = (∑ i ∈ Finset.range 47, stT256 (i+1)) + stT256 48 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 47
    simpa using h
  have hprev := st256_p47
  have hstep := st256_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p49 : ((1873067158191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT256 (i+1))
      = (∑ i ∈ Finset.range 48, stT256 (i+1)) + stT256 49 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 48
    simpa using h
  have hprev := st256_p48
  have hstep := st256_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p50 : ((3536571136113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT256 (i+1))
      = (∑ i ∈ Finset.range 49, stT256 (i+1)) + stT256 50 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 49
    simpa using h
  have hprev := st256_p49
  have hstep := st256_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p51 : ((4090537307193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT256 (i+1))
      = (∑ i ∈ Finset.range 50, stT256 (i+1)) + stT256 51 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 50
    simpa using h
  have hprev := st256_p50
  have hstep := st256_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p52 : ((4640702634693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT256 (i+1))
      = (∑ i ∈ Finset.range 51, stT256 (i+1)) + stT256 52 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 51
    simpa using h
  have hprev := st256_p51
  have hstep := st256_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p53 : ((2158632218747/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT256 (i+1))
      = (∑ i ∈ Finset.range 52, stT256 (i+1)) + stT256 53 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 52
    simpa using h
  have hprev := st256_p52
  have hstep := st256_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p54 : ((1847630628869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT256 (i+1))
      = (∑ i ∈ Finset.range 53, stT256 (i+1)) + stT256 54 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 53
    simpa using h
  have hprev := st256_p53
  have hstep := st256_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p55 : ((1988913179291/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT256 (i+1))
      = (∑ i ∈ Finset.range 54, stT256 (i+1)) + stT256 55 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 54
    simpa using h
  have hprev := st256_p54
  have hstep := st256_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p56 : ((91070887999/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT256 (i+1))
      = (∑ i ∈ Finset.range 55, stT256 (i+1)) + stT256 56 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 55
    simpa using h
  have hprev := st256_p55
  have hstep := st256_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p57 : ((8240170030603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT256 (i+1))
      = (∑ i ∈ Finset.range 56, stT256 (i+1)) + stT256 57 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 56
    simpa using h
  have hprev := st256_p56
  have hstep := st256_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p58 : ((7501683891693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT256 (i+1))
      = (∑ i ∈ Finset.range 57, stT256 (i+1)) + stT256 58 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 57
    simpa using h
  have hprev := st256_p57
  have hstep := st256_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p59 : ((4379704455573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT256 (i+1))
      = (∑ i ∈ Finset.range 58, stT256 (i+1)) + stT256 59 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 58
    simpa using h
  have hprev := st256_p58
  have hstep := st256_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p60 : ((535500858651/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT256 (i+1))
      = (∑ i ∈ Finset.range 59, stT256 (i+1)) + stT256 60 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 59
    simpa using h
  have hprev := st256_p59
  have hstep := st256_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p61 : ((301324222391/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT256 (i+1))
      = (∑ i ∈ Finset.range 60, stT256 (i+1)) + stT256 61 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 60
    simpa using h
  have hprev := st256_p60
  have hstep := st256_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p62 : ((54418586463/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT256 (i+1))
      = (∑ i ∈ Finset.range 61, stT256 (i+1)) + stT256 62 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 61
    simpa using h
  have hprev := st256_p61
  have hstep := st256_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p63 : ((131656722299/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT256 (i+1))
      = (∑ i ∈ Finset.range 62, stT256 (i+1)) + stT256 63 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 62
    simpa using h
  have hprev := st256_p62
  have hstep := st256_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p64 : ((1913626152479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT256 (i+1))
      = (∑ i ∈ Finset.range 63, stT256 (i+1)) + stT256 64 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 63
    simpa using h
  have hprev := st256_p63
  have hstep := st256_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p65 : ((2222750393207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT256 (i+1))
      = (∑ i ∈ Finset.range 64, stT256 (i+1)) + stT256 65 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 64
    simpa using h
  have hprev := st256_p64
  have hstep := st256_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p66 : ((3970297434259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT256 (i+1))
      = (∑ i ∈ Finset.range 65, stT256 (i+1)) + stT256 66 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 65
    simpa using h
  have hprev := st256_p65
  have hstep := st256_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p67 : ((4076002064221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT256 (i+1))
      = (∑ i ∈ Finset.range 66, stT256 (i+1)) + stT256 67 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 66
    simpa using h
  have hprev := st256_p66
  have hstep := st256_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p68 : ((2177202823883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT256 (i+1))
      = (∑ i ∈ Finset.range 67, stT256 (i+1)) + stT256 68 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 67
    simpa using h
  have hprev := st256_p67
  have hstep := st256_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p69 : ((1912777602251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT256 (i+1))
      = (∑ i ∈ Finset.range 68, stT256 (i+1)) + stT256 69 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 68
    simpa using h
  have hprev := st256_p68
  have hstep := st256_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p70 : ((2211281611953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT256 (i+1))
      = (∑ i ∈ Finset.range 69, stT256 (i+1)) + stT256 70 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 69
    simpa using h
  have hprev := st256_p69
  have hstep := st256_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p71 : ((1955814918633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT256 (i+1))
      = (∑ i ∈ Finset.range 70, stT256 (i+1)) + stT256 71 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 70
    simpa using h
  have hprev := st256_p70
  have hstep := st256_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p72 : ((8486995891221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT256 (i+1))
      = (∑ i ∈ Finset.range 71, stT256 (i+1)) + stT256 72 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 71
    simpa using h
  have hprev := st256_p71
  have hstep := st256_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p73 : ((8244303940549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT256 (i+1))
      = (∑ i ∈ Finset.range 72, stT256 (i+1)) + stT256 73 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 72
    simpa using h
  have hprev := st256_p72
  have hstep := st256_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p74 : ((1618105831607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT256 (i+1))
      = (∑ i ∈ Finset.range 73, stT256 (i+1)) + stT256 74 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 73
    simpa using h
  have hprev := st256_p73
  have hstep := st256_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p75 : ((1713808060427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT256 (i+1))
      = (∑ i ∈ Finset.range 74, stT256 (i+1)) + stT256 75 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 74
    simpa using h
  have hprev := st256_p74
  have hstep := st256_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p76 : ((1962704071657/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT256 (i+1))
      = (∑ i ∈ Finset.range 75, stT256 (i+1)) + stT256 76 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 75
    simpa using h
  have hprev := st256_p75
  have hstep := st256_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p77 : ((8730102456083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT256 (i+1))
      = (∑ i ∈ Finset.range 76, stT256 (i+1)) + stT256 77 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 76
    simpa using h
  have hprev := st256_p76
  have hstep := st256_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p78 : ((1550362626361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT256 (i+1))
      = (∑ i ∈ Finset.range 77, stT256 (i+1)) + stT256 78 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 77
    simpa using h
  have hprev := st256_p77
  have hstep := st256_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p79 : ((351377169251/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT256 (i+1))
      = (∑ i ∈ Finset.range 78, stT256 (i+1)) + stT256 79 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 78
    simpa using h
  have hprev := st256_p78
  have hstep := st256_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p80 : ((7726507447319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT256 (i+1))
      = (∑ i ∈ Finset.range 79, stT256 (i+1)) + stT256 80 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 79
    simpa using h
  have hprev := st256_p79
  have hstep := st256_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p81 : ((4395425337109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT256 (i+1))
      = (∑ i ∈ Finset.range 80, stT256 (i+1)) + stT256 81 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 80
    simpa using h
  have hprev := st256_p80
  have hstep := st256_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p82 : ((3866523679911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT256 (i+1))
      = (∑ i ∈ Finset.range 81, stT256 (i+1)) + stT256 82 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 81
    simpa using h
  have hprev := st256_p81
  have hstep := st256_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p83 : ((2192856093829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT256 (i+1))
      = (∑ i ∈ Finset.range 82, stT256 (i+1)) + stT256 83 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 82
    simpa using h
  have hprev := st256_p82
  have hstep := st256_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p84 : ((971103540107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT256 (i+1))
      = (∑ i ∈ Finset.range 83, stT256 (i+1)) + stT256 84 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 83
    simpa using h
  have hprev := st256_p83
  have hstep := st256_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p85 : ((544458271103/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT256 (i+1))
      = (∑ i ∈ Finset.range 84, stT256 (i+1)) + stT256 85 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 84
    simpa using h
  have hprev := st256_p84
  have hstep := st256_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p86 : ((982844247457/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT256 (i+1))
      = (∑ i ∈ Finset.range 85, stT256 (i+1)) + stT256 86 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 85
    simpa using h
  have hprev := st256_p85
  have hstep := st256_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p87 : ((1071581483543/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT256 (i+1))
      = (∑ i ∈ Finset.range 86, stT256 (i+1)) + stT256 87 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 86
    simpa using h
  have hprev := st256_p86
  have hstep := st256_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p88 : ((2013537680189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT256 (i+1))
      = (∑ i ∈ Finset.range 87, stT256 (i+1)) + stT256 88 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 87
    simpa using h
  have hprev := st256_p87
  have hstep := st256_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p89 : ((2081390208153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT256 (i+1))
      = (∑ i ∈ Finset.range 88, stT256 (i+1)) + stT256 89 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 88
    simpa using h
  have hprev := st256_p88
  have hstep := st256_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p90 : ((2087238310569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT256 (i+1))
      = (∑ i ∈ Finset.range 89, stT256 (i+1)) + stT256 90 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 89
    simpa using h
  have hprev := st256_p89
  have hstep := st256_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p91 : ((4002091394313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT256 (i+1))
      = (∑ i ∈ Finset.range 90, stT256 (i+1)) + stT256 91 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 90
    simpa using h
  have hprev := st256_p90
  have hstep := st256_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p92 : ((4329372468837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT256 (i+1))
      = (∑ i ∈ Finset.range 91, stT256 (i+1)) + stT256 92 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 91
    simpa using h
  have hprev := st256_p91
  have hstep := st256_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p93 : ((3878879560433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT256 (i+1))
      = (∑ i ∈ Finset.range 92, stT256 (i+1)) + stT256 93 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 92
    simpa using h
  have hprev := st256_p92
  have hstep := st256_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p94 : ((8782390276423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT256 (i+1))
      = (∑ i ∈ Finset.range 93, stT256 (i+1)) + stT256 94 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 93
    simpa using h
  have hprev := st256_p93
  have hstep := st256_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p95 : ((7807866175231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT256 (i+1))
      = (∑ i ∈ Finset.range 94, stT256 (i+1)) + stT256 95 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 94
    simpa using h
  have hprev := st256_p94
  have hstep := st256_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p96 : ((8533999542291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT256 (i+1))
      = (∑ i ∈ Finset.range 95, stT256 (i+1)) + stT256 96 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 95
    simpa using h
  have hprev := st256_p95
  have hstep := st256_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p97 : ((4115524721277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT256 (i+1))
      = (∑ i ∈ Finset.range 96, stT256 (i+1)) + stT256 97 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 96
    simpa using h
  have hprev := st256_p96
  have hstep := st256_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p98 : ((8017463702387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT256 (i+1))
      = (∑ i ∈ Finset.range 97, stT256 (i+1)) + stT256 98 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 97
    simpa using h
  have hprev := st256_p97
  have hstep := st256_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p99 : ((1088321794587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT256 (i+1))
      = (∑ i ∈ Finset.range 98, stT256 (i+1)) + stT256 99 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 98
    simpa using h
  have hprev := st256_p98
  have hstep := st256_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p100 : ((967094169587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT256 (i+1))
      = (∑ i ∈ Finset.range 99, stT256 (i+1)) + stT256 100 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 99
    simpa using h
  have hprev := st256_p99
  have hstep := st256_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p101 : ((1084020967457/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT256 (i+1))
      = (∑ i ∈ Finset.range 100, stT256 (i+1)) + stT256 101 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 100
    simpa using h
  have hprev := st256_p100
  have hstep := st256_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p102 : ((405504669747/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT256 (i+1))
      = (∑ i ∈ Finset.range 101, stT256 (i+1)) + stT256 102 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 101
    simpa using h
  have hprev := st256_p101
  have hstep := st256_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p103 : ((807022595781/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT256 (i+1))
      = (∑ i ∈ Finset.range 102, stT256 (i+1)) + stT256 103 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 102
    simpa using h
  have hprev := st256_p102
  have hstep := st256_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p104 : ((174165748053/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT256 (i+1))
      = (∑ i ∈ Finset.range 103, stT256 (i+1)) + stT256 104 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 103
    simpa using h
  have hprev := st256_p103
  have hstep := st256_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p105 : ((968309557661/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT256 (i+1))
      = (∑ i ∈ Finset.range 104, stT256 (i+1)) + stT256 105 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 104
    simpa using h
  have hprev := st256_p104
  have hstep := st256_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p106 : ((8577192239663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT256 (i+1))
      = (∑ i ∈ Finset.range 105, stT256 (i+1)) + stT256 106 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 105
    simpa using h
  have hprev := st256_p105
  have hstep := st256_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p107 : ((1660441940087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT256 (i+1))
      = (∑ i ∈ Finset.range 106, stT256 (i+1)) + stT256 107 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 106
    simpa using h
  have hprev := st256_p106
  have hstep := st256_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p108 : ((7864824281891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT256 (i+1))
      = (∑ i ∈ Finset.range 107, stT256 (i+1)) + stT256 108 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 107
    simpa using h
  have hprev := st256_p107
  have hstep := st256_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p109 : ((8774923727963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT256 (i+1))
      = (∑ i ∈ Finset.range 108, stT256 (i+1)) + stT256 109 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 108
    simpa using h
  have hprev := st256_p108
  have hstep := st256_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p110 : ((1983045881441/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT256 (i+1))
      = (∑ i ∈ Finset.range 109, stT256 (i+1)) + stT256 110 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 109
    simpa using h
  have hprev := st256_p109
  have hstep := st256_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p111 : ((1635073977641/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT256 (i+1))
      = (∑ i ∈ Finset.range 110, stT256 (i+1)) + stT256 111 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 110
    simpa using h
  have hprev := st256_p110
  have hstep := st256_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p112 : ((1739652947477/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT256 (i+1))
      = (∑ i ∈ Finset.range 111, stT256 (i+1)) + stT256 112 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 111
    simpa using h
  have hprev := st256_p111
  have hstep := st256_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p113 : ((3882036640923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT256 (i+1))
      = (∑ i ∈ Finset.range 112, stT256 (i+1)) + stT256 113 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 112
    simpa using h
  have hprev := st256_p112
  have hstep := st256_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p114 : ((8437864706451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT256 (i+1))
      = (∑ i ∈ Finset.range 113, stT256 (i+1)) + stT256 114 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 113
    simpa using h
  have hprev := st256_p113
  have hstep := st256_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p115 : ((341338078459/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT256 (i+1))
      = (∑ i ∈ Finset.range 114, stT256 (i+1)) + stT256 115 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 114
    simpa using h
  have hprev := st256_p114
  have hstep := st256_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p116 : ((3869218515443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT256 (i+1))
      = (∑ i ∈ Finset.range 115, stT256 (i+1)) + stT256 116 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 115
    simpa using h
  have hprev := st256_p115
  have hstep := st256_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p117 : ((4294734894693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT256 (i+1))
      = (∑ i ∈ Finset.range 116, stT256 (i+1)) + stT256 117 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 116
    simpa using h
  have hprev := st256_p116
  have hstep := st256_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p118 : ((8400476662461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT256 (i+1))
      = (∑ i ∈ Finset.range 117, stT256 (i+1)) + stT256 118 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 117
    simpa using h
  have hprev := st256_p117
  have hstep := st256_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p119 : ((38796508153/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT256 (i+1))
      = (∑ i ∈ Finset.range 118, stT256 (i+1)) + stT256 119 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 118
    simpa using h
  have hprev := st256_p118
  have hstep := st256_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p120 : ((173067421459/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT256 (i+1))
      = (∑ i ∈ Finset.range 119, stT256 (i+1)) + stT256 120 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 119
    simpa using h
  have hprev := st256_p119
  have hstep := st256_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p121 : ((8341051950809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT256 (i+1))
      = (∑ i ∈ Finset.range 120, stT256 (i+1)) + stT256 121 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 120
    simpa using h
  have hprev := st256_p120
  have hstep := st256_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p122 : ((1553790702907/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT256 (i+1))
      = (∑ i ∈ Finset.range 121, stT256 (i+1)) + stT256 122 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 121
    simpa using h
  have hprev := st256_p121
  have hstep := st256_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p123 : ((4329170440543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT256 (i+1))
      = (∑ i ∈ Finset.range 122, stT256 (i+1)) + stT256 123 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 122
    simpa using h
  have hprev := st256_p122
  have hstep := st256_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p124 : ((4180613426041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT256 (i+1))
      = (∑ i ∈ Finset.range 123, stT256 (i+1)) + stT256 124 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 123
    simpa using h
  have hprev := st256_p123
  have hstep := st256_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p125 : ((3876343331289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT256 (i+1))
      = (∑ i ∈ Finset.range 124, stT256 (i+1)) + stT256 125 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 124
    simpa using h
  have hprev := st256_p124
  have hstep := st256_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p126 : ((538064437233/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT256 (i+1))
      = (∑ i ∈ Finset.range 125, stT256 (i+1)) + stT256 126 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 125
    simpa using h
  have hprev := st256_p125
  have hstep := st256_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p127 : ((8455559940507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT256 (i+1))
      = (∑ i ∈ Finset.range 126, stT256 (i+1)) + stT256 127 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 126
    simpa using h
  have hprev := st256_p126
  have hstep := st256_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p128 : ((7731467141679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT256 (i+1))
      = (∑ i ∈ Finset.range 127, stT256 (i+1)) + stT256 128 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 127
    simpa using h
  have hprev := st256_p127
  have hstep := st256_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p129 : ((8487265672029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT256 (i+1))
      = (∑ i ∈ Finset.range 128, stT256 (i+1)) + stT256 129 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 128
    simpa using h
  have hprev := st256_p128
  have hstep := st256_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p130 : ((8603070656233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT256 (i+1))
      = (∑ i ∈ Finset.range 129, stT256 (i+1)) + stT256 130 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 129
    simpa using h
  have hprev := st256_p129
  have hstep := st256_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p131 : ((7758335966623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT256 (i+1))
      = (∑ i ∈ Finset.range 130, stT256 (i+1)) + stT256 131 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 130
    simpa using h
  have hprev := st256_p130
  have hstep := st256_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p132 : ((66193399171/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT256 (i+1))
      = (∑ i ∈ Finset.range 131, stT256 (i+1)) + stT256 132 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 131
    simpa using h
  have hprev := st256_p131
  have hstep := st256_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p133 : ((8745765999769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT256 (i+1))
      = (∑ i ∈ Finset.range 132, stT256 (i+1)) + stT256 133 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 132
    simpa using h
  have hprev := st256_p132
  have hstep := st256_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p134 : ((1976066721881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT256 (i+1))
      = (∑ i ∈ Finset.range 133, stT256 (i+1)) + stT256 134 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 133
    simpa using h
  have hprev := st256_p133
  have hstep := st256_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p135 : ((3996898626037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT256 (i+1))
      = (∑ i ∈ Finset.range 134, stT256 (i+1)) + stT256 135 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 134
    simpa using h
  have hprev := st256_p134
  have hstep := st256_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p136 : ((4387874247167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT256 (i+1))
      = (∑ i ∈ Finset.range 135, stT256 (i+1)) + stT256 136 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 135
    simpa using h
  have hprev := st256_p135
  have hstep := st256_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p137 : ((4103789959871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT256 (i+1))
      = (∑ i ∈ Finset.range 136, stT256 (i+1)) + stT256 137 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 136
    simpa using h
  have hprev := st256_p136
  have hstep := st256_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p138 : ((776091175173/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT256 (i+1))
      = (∑ i ∈ Finset.range 137, stT256 (i+1)) + stT256 138 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 137
    simpa using h
  have hprev := st256_p137
  have hstep := st256_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p139 : ((4288625570259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT256 (i+1))
      = (∑ i ∈ Finset.range 138, stT256 (i+1)) + stT256 139 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 138
    simpa using h
  have hprev := st256_p138
  have hstep := st256_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p140 : ((5366240073/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT256 (i+1))
      = (∑ i ∈ Finset.range 139, stT256 (i+1)) + stT256 140 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 139
    simpa using h
  have hprev := st256_p139
  have hstep := st256_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p141 : ((48550643359/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT256 (i+1))
      = (∑ i ∈ Finset.range 140, stT256 (i+1)) + stT256 141 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 140
    simpa using h
  have hprev := st256_p140
  have hstep := st256_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p142 : ((2038760645773/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT256 (i+1))
      = (∑ i ∈ Finset.range 141, stT256 (i+1)) + stT256 142 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 141
    simpa using h
  have hprev := st256_p141
  have hstep := st256_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p143 : ((4395948447153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT256 (i+1))
      = (∑ i ∈ Finset.range 142, stT256 (i+1)) + stT256 143 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 142
    simpa using h
  have hprev := st256_p142
  have hstep := st256_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p144 : ((2032446382821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT256 (i+1))
      = (∑ i ∈ Finset.range 143, stT256 (i+1)) + stT256 144 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 143
    simpa using h
  have hprev := st256_p143
  have hstep := st256_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p145 : ((7767188116909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT256 (i+1))
      = (∑ i ∈ Finset.range 144, stT256 (i+1)) + stT256 145 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 144
    simpa using h
  have hprev := st256_p144
  have hstep := st256_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p146 : ((4283134027687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT256 (i+1))
      = (∑ i ∈ Finset.range 145, stT256 (i+1)) + stT256 146 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 145
    simpa using h
  have hprev := st256_p145
  have hstep := st256_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p147 : ((4318735915377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT256 (i+1))
      = (∑ i ∈ Finset.range 146, stT256 (i+1)) + stT256 147 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 146
    simpa using h
  have hprev := st256_p146
  have hstep := st256_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p148 : ((7817955145679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT256 (i+1))
      = (∑ i ∈ Finset.range 147, stT256 (i+1)) + stT256 148 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 147
    simpa using h
  have hprev := st256_p147
  have hstep := st256_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p149 : ((160116768049/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT256 (i+1))
      = (∑ i ∈ Finset.range 148, stT256 (i+1)) + stT256 149 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 148
    simpa using h
  have hprev := st256_p148
  have hstep := st256_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p150 : ((4383072798609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT256 (i+1))
      = (∑ i ∈ Finset.range 149, stT256 (i+1)) + stT256 150 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 149
    simpa using h
  have hprev := st256_p149
  have hstep := st256_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p151 : ((8373644583261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT256 (i+1))
      = (∑ i ∈ Finset.range 150, stT256 (i+1)) + stT256 151 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 150
    simpa using h
  have hprev := st256_p150
  have hstep := st256_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p152 : ((1542901642293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT256 (i+1))
      = (∑ i ∈ Finset.range 151, stT256 (i+1)) + stT256 152 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 151
    simpa using h
  have hprev := st256_p151
  have hstep := st256_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p153 : ((8253670509429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT256 (i+1))
      = (∑ i ∈ Finset.range 152, stT256 (i+1)) + stT256 153 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 152
    simpa using h
  have hprev := st256_p152
  have hstep := st256_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p154 : ((8799191857879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT256 (i+1))
      = (∑ i ∈ Finset.range 153, stT256 (i+1)) + stT256 154 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 153
    simpa using h
  have hprev := st256_p153
  have hstep := st256_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p155 : ((8163408689419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT256 (i+1))
      = (∑ i ∈ Finset.range 154, stT256 (i+1)) + stT256 155 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 154
    simpa using h
  have hprev := st256_p154
  have hstep := st256_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p156 : ((1930809070911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT256 (i+1))
      = (∑ i ∈ Finset.range 155, stT256 (i+1)) + stT256 156 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 155
    simpa using h
  have hprev := st256_p155
  have hstep := st256_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p157 : ((4208480283927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT256 (i+1))
      = (∑ i ∈ Finset.range 156, stT256 (i+1)) + stT256 157 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 156
    simpa using h
  have hprev := st256_p156
  have hstep := st256_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p158 : ((8771848203313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT256 (i+1))
      = (∑ i ∈ Finset.range 157, stT256 (i+1)) + stT256 158 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 157
    simpa using h
  have hprev := st256_p157
  have hstep := st256_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p159 : ((8047063705577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT256 (i+1))
      = (∑ i ∈ Finset.range 158, stT256 (i+1)) + stT256 159 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 158
    simpa using h
  have hprev := st256_p158
  have hstep := st256_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p160 : ((7750950968657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT256 (i+1))
      = (∑ i ∈ Finset.range 159, stT256 (i+1)) + stT256 160 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 159
    simpa using h
  have hprev := st256_p159
  have hstep := st256_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p161 : ((8488597497247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT256 (i+1))
      = (∑ i ∈ Finset.range 160, stT256 (i+1)) + stT256 161 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 160
    simpa using h
  have hprev := st256_p160
  have hstep := st256_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p162 : ((8754490006371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT256 (i+1))
      = (∑ i ∈ Finset.range 161, stT256 (i+1)) + stT256 162 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 161
    simpa using h
  have hprev := st256_p161
  have hstep := st256_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p163 : ((4008104667909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT256 (i+1))
      = (∑ i ∈ Finset.range 162, stT256 (i+1)) + stT256 163 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 162
    simpa using h
  have hprev := st256_p162
  have hstep := st256_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p164 : ((60558882123/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT256 (i+1))
      = (∑ i ∈ Finset.range 163, stT256 (i+1)) + stT256 164 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 163
    simpa using h
  have hprev := st256_p163
  have hstep := st256_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p165 : ((530000344767/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT256 (i+1))
      = (∑ i ∈ Finset.range 164, stT256 (i+1)) + stT256 165 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 164
    simpa using h
  have hprev := st256_p164
  have hstep := st256_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p166 : ((4385470731511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT256 (i+1))
      = (∑ i ∈ Finset.range 165, stT256 (i+1)) + stT256 166 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 165
    simpa using h
  have hprev := st256_p165
  have hstep := st256_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p167 : ((806355180107/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT256 (i+1))
      = (∑ i ∈ Finset.range 166, stT256 (i+1)) + stT256 167 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 166
    simpa using h
  have hprev := st256_p166
  have hstep := st256_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p168 : ((386051069929/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT256 (i+1))
      = (∑ i ∈ Finset.range 167, stT256 (i+1)) + stT256 168 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 167
    simpa using h
  have hprev := st256_p167
  have hstep := st256_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p169 : ((839177688167/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT256 (i+1))
      = (∑ i ∈ Finset.range 168, stT256 (i+1)) + stT256 169 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 168
    simpa using h
  have hprev := st256_p168
  have hstep := st256_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p170 : ((4403431200127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT256 (i+1))
      = (∑ i ∈ Finset.range 169, stT256 (i+1)) + stT256 170 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 169
    simpa using h
  have hprev := st256_p169
  have hstep := st256_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p171 : ((4097010572647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT256 (i+1))
      = (∑ i ∈ Finset.range 170, stT256 (i+1)) + stT256 171 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 170
    simpa using h
  have hprev := st256_p170
  have hstep := st256_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p172 : ((1538316344079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT256 (i+1))
      = (∑ i ∈ Finset.range 171, stT256 (i+1)) + stT256 172 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 171
    simpa using h
  have hprev := st256_p171
  have hstep := st256_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p173 : ((821791105991/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT256 (i+1))
      = (∑ i ∈ Finset.range 172, stT256 (i+1)) + stT256 173 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 172
    simpa using h
  have hprev := st256_p172
  have hstep := st256_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p174 : ((176247168893/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT256 (i+1))
      = (∑ i ∈ Finset.range 173, stT256 (i+1)) + stT256 174 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 173
    simpa using h
  have hprev := st256_p173
  have hstep := st256_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p175 : ((4203573619887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT256 (i+1))
      = (∑ i ∈ Finset.range 174, stT256 (i+1)) + stT256 175 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 174
    simpa using h
  have hprev := st256_p174
  have hstep := st256_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p176 : ((7729548914409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT256 (i+1))
      = (∑ i ∈ Finset.range 175, stT256 (i+1)) + stT256 176 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 175
    simpa using h
  have hprev := st256_p175
  have hstep := st256_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p177 : ((7975369477187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT256 (i+1))
      = (∑ i ∈ Finset.range 176, stT256 (i+1)) + stT256 177 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 176
    simpa using h
  have hprev := st256_p176
  have hstep := st256_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p178 : ((8709217290543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT256 (i+1))
      = (∑ i ∈ Finset.range 177, stT256 (i+1)) + stT256 178 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 177
    simpa using h
  have hprev := st256_p177
  have hstep := st256_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p179 : ((8658337827151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT256 (i+1))
      = (∑ i ∈ Finset.range 178, stT256 (i+1)) + stT256 179 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 178
    simpa using h
  have hprev := st256_p178
  have hstep := st256_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p180 : ((7915126961719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT256 (i+1))
      = (∑ i ∈ Finset.range 179, stT256 (i+1)) + stT256 180 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 179
    simpa using h
  have hprev := st256_p179
  have hstep := st256_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p181 : ((3873161218667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT256 (i+1))
      = (∑ i ∈ Finset.range 180, stT256 (i+1)) + stT256 181 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 180
    simpa using h
  have hprev := st256_p180
  have hstep := st256_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p182 : ((8432045215993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT256 (i+1))
      = (∑ i ∈ Finset.range 181, stT256 (i+1)) + stT256 182 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 181
    simpa using h
  have hprev := st256_p181
  have hstep := st256_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p183 : ((8823063556153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT256 (i+1))
      = (∑ i ∈ Finset.range 182, stT256 (i+1)) + stT256 183 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 182
    simpa using h
  have hprev := st256_p182
  have hstep := st256_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p184 : ((8275219214433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT256 (i+1))
      = (∑ i ∈ Finset.range 183, stT256 (i+1)) + stT256 184 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 183
    simpa using h
  have hprev := st256_p183
  have hstep := st256_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p185 : ((7691858461393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT256 (i+1))
      = (∑ i ∈ Finset.range 184, stT256 (i+1)) + stT256 185 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 184
    simpa using h
  have hprev := st256_p184
  have hstep := st256_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p186 : ((8019743555753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT256 (i+1))
      = (∑ i ∈ Finset.range 185, stT256 (i+1)) + stT256 186 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 185
    simpa using h
  have hprev := st256_p185
  have hstep := st256_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p187 : ((8725349371097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT256 (i+1))
      = (∑ i ∈ Finset.range 186, stT256 (i+1)) + stT256 187 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 186
    simpa using h
  have hprev := st256_p186
  have hstep := st256_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p188 : ((4340766127211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT256 (i+1))
      = (∑ i ∈ Finset.range 187, stT256 (i+1)) + stT256 188 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 187
    simpa using h
  have hprev := st256_p187
  have hstep := st256_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p189 : ((7962558828397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT256 (i+1))
      = (∑ i ∈ Finset.range 188, stT256 (i+1)) + stT256 189 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 188
    simpa using h
  have hprev := st256_p188
  have hstep := st256_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p190 : ((7698482298489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT256 (i+1))
      = (∑ i ∈ Finset.range 189, stT256 (i+1)) + stT256 190 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 189
    simpa using h
  have hprev := st256_p189
  have hstep := st256_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p191 : ((8295858480723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT256 (i+1))
      = (∑ i ∈ Finset.range 190, stT256 (i+1)) + stT256 191 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 190
    simpa using h
  have hprev := st256_p190
  have hstep := st256_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p192 : ((4415027403279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT256 (i+1))
      = (∑ i ∈ Finset.range 191, stT256 (i+1)) + stT256 192 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 191
    simpa using h
  have hprev := st256_p191
  have hstep := st256_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p193 : ((4243592425639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT256 (i+1))
      = (∑ i ∈ Finset.range 192, stT256 (i+1)) + stT256 193 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 192
    simpa using h
  have hprev := st256_p192
  have hstep := st256_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p194 : ((3895633596289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT256 (i+1))
      = (∑ i ∈ Finset.range 193, stT256 (i+1)) + stT256 194 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 193
    simpa using h
  have hprev := st256_p193
  have hstep := st256_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p195 : ((7786958328623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT256 (i+1))
      = (∑ i ∈ Finset.range 194, stT256 (i+1)) + stT256 195 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 194
    simpa using h
  have hprev := st256_p194
  have hstep := st256_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p196 : ((8475841925453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT256 (i+1))
      = (∑ i ∈ Finset.range 195, stT256 (i+1)) + stT256 196 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 195
    simpa using h
  have hprev := st256_p195
  have hstep := st256_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p197 : ((8839227274373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT256 (i+1))
      = (∑ i ∈ Finset.range 196, stT256 (i+1)) + stT256 197 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 196
    simpa using h
  have hprev := st256_p196
  have hstep := st256_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p198 : ((8349122236913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT256 (i+1))
      = (∑ i ∈ Finset.range 197, stT256 (i+1)) + stT256 198 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 197
    simpa using h
  have hprev := st256_p197
  have hstep := st256_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p199 : ((7720246786079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT256 (i+1))
      = (∑ i ∈ Finset.range 198, stT256 (i+1)) + stT256 199 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 198
    simpa using h
  have hprev := st256_p198
  have hstep := st256_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p200 : ((7855284940217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT256 (i+1))
      = (∑ i ∈ Finset.range 199, stT256 (i+1)) + stT256 200 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 199
    simpa using h
  have hprev := st256_p199
  have hstep := st256_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p201 : ((8556945217937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT256 (i+1))
      = (∑ i ∈ Finset.range 200, stT256 (i+1)) + stT256 201 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 200
    simpa using h
  have hprev := st256_p200
  have hstep := st256_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p202 : ((8832271167201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT256 (i+1))
      = (∑ i ∈ Finset.range 201, stT256 (i+1)) + stT256 202 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 201
    simpa using h
  have hprev := st256_p201
  have hstep := st256_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p203 : ((829937677141/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT256 (i+1))
      = (∑ i ∈ Finset.range 202, stT256 (i+1)) + stT256 203 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 202
    simpa using h
  have hprev := st256_p202
  have hstep := st256_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p204 : ((385109575273/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT256 (i+1))
      = (∑ i ∈ Finset.range 203, stT256 (i+1)) + stT256 204 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 203
    simpa using h
  have hprev := st256_p203
  have hstep := st256_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p205 : ((393080198119/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT256 (i+1))
      = (∑ i ∈ Finset.range 204, stT256 (i+1)) + stT256 205 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 204
    simpa using h
  have hprev := st256_p204
  have hstep := st256_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p206 : ((8555178671691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT256 (i+1))
      = (∑ i ∈ Finset.range 205, stT256 (i+1)) + stT256 206 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 205
    simpa using h
  have hprev := st256_p205
  have hstep := st256_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p207 : ((1768448506263/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT256 (i+1))
      = (∑ i ∈ Finset.range 206, stT256 (i+1)) + stT256 207 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 206
    simpa using h
  have hprev := st256_p206
  have hstep := st256_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p208 : ((1668199510807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT256 (i+1))
      = (∑ i ∈ Finset.range 207, stT256 (i+1)) + stT256 208 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 207
    simpa using h
  have hprev := st256_p207
  have hstep := st256_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p209 : ((772267974097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT256 (i+1))
      = (∑ i ∈ Finset.range 208, stT256 (i+1)) + stT256 209 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 208
    simpa using h
  have hprev := st256_p208
  have hstep := st256_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p210 : ((97532486611/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT256 (i+1))
      = (∑ i ∈ Finset.range 209, stT256 (i+1)) + stT256 210 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 209
    simpa using h
  have hprev := st256_p209
  have hstep := st256_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p211 : ((2117875605593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT256 (i+1))
      = (∑ i ∈ Finset.range 210, stT256 (i+1)) + stT256 211 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 210
    simpa using h
  have hprev := st256_p210
  have hstep := st256_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p212 : ((4429326698287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT256 (i+1))
      = (∑ i ∈ Finset.range 211, stT256 (i+1)) + stT256 212 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 211
    simpa using h
  have hprev := st256_p211
  have hstep := st256_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p213 : ((529279018641/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT256 (i+1))
      = (∑ i ∈ Finset.range 212, stT256 (i+1)) + stT256 213 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 212
    simpa using h
  have hprev := st256_p212
  have hstep := st256_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p214 : ((975435688647/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT256 (i+1))
      = (∑ i ∈ Finset.range 213, stT256 (i+1)) + stT256 214 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 213
    simpa using h
  have hprev := st256_p213
  have hstep := st256_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p215 : ((7706087757241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT256 (i+1))
      = (∑ i ∈ Finset.range 214, stT256 (i+1)) + stT256 215 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 214
    simpa using h
  have hprev := st256_p214
  have hstep := st256_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p216 : ((2073613451547/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT256 (i+1))
      = (∑ i ∈ Finset.range 215, stT256 (i+1)) + stT256 216 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 215
    simpa using h
  have hprev := st256_p215
  have hstep := st256_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p217 : ((2208056129793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT256 (i+1))
      = (∑ i ∈ Finset.range 216, stT256 (i+1)) + stT256 217 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 216
    simpa using h
  have hprev := st256_p216
  have hstep := st256_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p218 : ((4328203584573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT256 (i+1))
      = (∑ i ∈ Finset.range 217, stT256 (i+1)) + stT256 218 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 217
    simpa using h
  have hprev := st256_p217
  have hstep := st256_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p219 : ((998366404149/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT256 (i+1))
      = (∑ i ∈ Finset.range 218, stT256 (i+1)) + stT256 219 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 218
    simpa using h
  have hprev := st256_p218
  have hstep := st256_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p220 : ((119369006703/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT256 (i+1))
      = (∑ i ∈ Finset.range 219, stT256 (i+1)) + stT256 220 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 219
    simpa using h
  have hprev := st256_p219
  have hstep := st256_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p221 : ((125474472069/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT256 (i+1))
      = (∑ i ∈ Finset.range 220, stT256 (i+1)) + stT256 221 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 220
    simpa using h
  have hprev := st256_p220
  have hstep := st256_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p222 : ((1085932351199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT256 (i+1))
      = (∑ i ∈ Finset.range 221, stT256 (i+1)) + stT256 222 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 221
    simpa using h
  have hprev := st256_p221
  have hstep := st256_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p223 : ((8830556774051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT256 (i+1))
      = (∑ i ∈ Finset.range 222, stT256 (i+1)) + stT256 223 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 222
    simpa using h
  have hprev := st256_p222
  have hstep := st256_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p224 : ((8294910407177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT256 (i+1))
      = (∑ i ∈ Finset.range 223, stT256 (i+1)) + stT256 224 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 223
    simpa using h
  have hprev := st256_p223
  have hstep := st256_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p225 : ((3854838723947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT256 (i+1))
      = (∑ i ∈ Finset.range 224, stT256 (i+1)) + stT256 225 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 224
    simpa using h
  have hprev := st256_p224
  have hstep := st256_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p226 : ((484511567779/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT256 (i+1))
      = (∑ i ∈ Finset.range 225, stT256 (i+1)) + stT256 226 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 225
    simpa using h
  have hprev := st256_p225
  have hstep := st256_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p227 : ((4184687232467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT256 (i+1))
      = (∑ i ∈ Finset.range 226, stT256 (i+1)) + stT256 227 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 226
    simpa using h
  have hprev := st256_p226
  have hstep := st256_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p228 : ((885448828353/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT256 (i+1))
      = (∑ i ∈ Finset.range 227, stT256 (i+1)) + stT256 228 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 227
    simpa using h
  have hprev := st256_p227
  have hstep := st256_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p229 : ((1732050090153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT256 (i+1))
      = (∑ i ∈ Finset.range 228, stT256 (i+1)) + stT256 229 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 228
    simpa using h
  have hprev := st256_p228
  have hstep := st256_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p230 : ((200223754123/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT256 (i+1))
      = (∑ i ∈ Finset.range 229, stT256 (i+1)) + stT256 230 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 229
    simpa using h
  have hprev := st256_p229
  have hstep := st256_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p231 : ((953515285463/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT256 (i+1))
      = (∑ i ∈ Finset.range 230, stT256 (i+1)) + stT256 231 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 230
    simpa using h
  have hprev := st256_p230
  have hstep := st256_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p232 : ((1984066558609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT256 (i+1))
      = (∑ i ∈ Finset.range 231, stT256 (i+1)) + stT256 232 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 231
    simpa using h
  have hprev := st256_p231
  have hstep := st256_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p233 : ((8591237211727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT256 (i+1))
      = (∑ i ∈ Finset.range 232, stT256 (i+1)) + stT256 233 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 232
    simpa using h
  have hprev := st256_p232
  have hstep := st256_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p234 : ((8878799487647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT256 (i+1))
      = (∑ i ∈ Finset.range 233, stT256 (i+1)) + stT256 234 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 233
    simpa using h
  have hprev := st256_p233
  have hstep := st256_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p235 : ((8491211689007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT256 (i+1))
      = (∑ i ∈ Finset.range 234, stT256 (i+1)) + stT256 235 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 234
    simpa using h
  have hprev := st256_p234
  have hstep := st256_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p236 : ((3923890273571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT256 (i+1))
      = (∑ i ∈ Finset.range 235, stT256 (i+1)) + stT256 236 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 235
    simpa using h
  have hprev := st256_p235
  have hstep := st256_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p237 : ((954201921179/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT256 (i+1))
      = (∑ i ∈ Finset.range 236, stT256 (i+1)) + stT256 237 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 236
    simpa using h
  have hprev := st256_p236
  have hstep := st256_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p238 : ((4035795938033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT256 (i+1))
      = (∑ i ∈ Finset.range 237, stT256 (i+1)) + stT256 238 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 237
    simpa using h
  have hprev := st256_p237
  have hstep := st256_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p239 : ((434958060921/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT256 (i+1))
      = (∑ i ∈ Finset.range 238, stT256 (i+1)) + stT256 239 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 238
    simpa using h
  have hprev := st256_p238
  have hstep := st256_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p240 : ((4431711710999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT256 (i+1))
      = (∑ i ∈ Finset.range 239, stT256 (i+1)) + stT256 240 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 239
    simpa using h
  have hprev := st256_p239
  have hstep := st256_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p241 : ((1679626028069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT256 (i+1))
      = (∑ i ∈ Finset.range 240, stT256 (i+1)) + stT256 241 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 240
    simpa using h
  have hprev := st256_p240
  have hstep := st256_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p242 : ((1556658491039/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT256 (i+1))
      = (∑ i ∈ Finset.range 241, stT256 (i+1)) + stT256 242 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 241
    simpa using h
  have hprev := st256_p241
  have hstep := st256_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p243 : ((3822012256299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT256 (i+1))
      = (∑ i ∈ Finset.range 242, stT256 (i+1)) + stT256 243 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 242
    simpa using h
  have hprev := st256_p242
  have hstep := st256_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p244 : ((4058752619591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT256 (i+1))
      = (∑ i ∈ Finset.range 243, stT256 (i+1)) + stT256 244 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 243
    simpa using h
  have hprev := st256_p243
  have hstep := st256_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p245 : ((4363066508043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT256 (i+1))
      = (∑ i ∈ Finset.range 244, stT256 (i+1)) + stT256 245 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 244
    simpa using h
  have hprev := st256_p244
  have hstep := st256_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p246 : ((886476371607/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT256 (i+1))
      = (∑ i ∈ Finset.range 245, stT256 (i+1)) + stT256 246 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 245
    simpa using h
  have hprev := st256_p245
  have hstep := st256_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p247 : ((83998162683/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT256 (i+1))
      = (∑ i ∈ Finset.range 246, stT256 (i+1)) + stT256 247 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 246
    simpa using h
  have hprev := st256_p246
  have hstep := st256_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p248 : ((3895007958993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT256 (i+1))
      = (∑ i ∈ Finset.range 247, stT256 (i+1)) + stT256 248 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 247
    simpa using h
  have hprev := st256_p247
  have hstep := st256_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p249 : ((3814214358743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT256 (i+1))
      = (∑ i ∈ Finset.range 248, stT256 (i+1)) + stT256 249 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 248
    simpa using h
  have hprev := st256_p248
  have hstep := st256_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p250 : ((8067898296151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT256 (i+1))
      = (∑ i ∈ Finset.range 249, stT256 (i+1)) + stT256 250 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 249
    simpa using h
  have hprev := st256_p249
  have hstep := st256_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p251 : ((1736784435911/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT256 (i+1))
      = (∑ i ∈ Finset.range 250, stT256 (i+1)) + stT256 251 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 250
    simpa using h
  have hprev := st256_p250
  have hstep := st256_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p252 : ((1778015898731/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT256 (i+1))
      = (∑ i ∈ Finset.range 251, stT256 (i+1)) + stT256 252 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 251
    simpa using h
  have hprev := st256_p251
  have hstep := st256_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p253 : ((849453289093/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT256 (i+1))
      = (∑ i ∈ Finset.range 252, stT256 (i+1)) + stT256 253 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 252
    simpa using h
  have hprev := st256_p252
  have hstep := st256_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p254 : ((3935759325977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT256 (i+1))
      = (∑ i ∈ Finset.range 253, stT256 (i+1)) + stT256 254 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 253
    simpa using h
  have hprev := st256_p253
  have hstep := st256_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p255 : ((3800842907077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT256 (i+1))
      = (∑ i ∈ Finset.range 254, stT256 (i+1)) + stT256 255 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 254
    simpa using h
  have hprev := st256_p254
  have hstep := st256_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p256 : ((3965905094577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT256 (i+1))
      = (∑ i ∈ Finset.range 255, stT256 (i+1)) + stT256 256 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 255
    simpa using h
  have hprev := st256_p255
  have hstep := st256_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p257 : ((855547866083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT256 (i+1))
      = (∑ i ∈ Finset.range 256, stT256 (i+1)) + stT256 257 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 256
    simpa using h
  have hprev := st256_p256
  have hstep := st256_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p258 : ((4451644546177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT256 (i+1))
      = (∑ i ∈ Finset.range 257, stT256 (i+1)) + stT256 258 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 257
    simpa using h
  have hprev := st256_p257
  have hstep := st256_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p259 : ((2165679404761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT256 (i+1))
      = (∑ i ∈ Finset.range 258, stT256 (i+1)) + stT256 259 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 258
    simpa using h
  have hprev := st256_p258
  have hstep := st256_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p260 : ((1006662334569/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT256 (i+1))
      = (∑ i ∈ Finset.range 259, stT256 (i+1)) + stT256 260 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 259
    simpa using h
  have hprev := st256_p259
  have hstep := st256_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p261 : ((1905056145833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT256 (i+1))
      = (∑ i ∈ Finset.range 260, stT256 (i+1)) + stT256 261 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 260
    simpa using h
  have hprev := st256_p260
  have hstep := st256_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p262 : ((3872715712831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT256 (i+1))
      = (∑ i ∈ Finset.range 261, stT256 (i+1)) + stT256 262 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 261
    simpa using h
  have hprev := st256_p261
  have hstep := st256_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p263 : ((10394233567/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT256 (i+1))
      = (∑ i ∈ Finset.range 262, stT256 (i+1)) + stT256 263 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 262
    simpa using h
  have hprev := st256_p262
  have hstep := st256_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p264 : ((275941423327/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT256 (i+1))
      = (∑ i ∈ Finset.range 263, stT256 (i+1)) + stT256 264 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 263
    simpa using h
  have hprev := st256_p263
  have hstep := st256_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p265 : ((4422057750397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT256 (i+1))
      = (∑ i ∈ Finset.range 264, stT256 (i+1)) + stT256 265 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 264
    simpa using h
  have hprev := st256_p264
  have hstep := st256_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p266 : ((4174216752157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT256 (i+1))
      = (∑ i ∈ Finset.range 265, stT256 (i+1)) + stT256 266 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 265
    simpa using h
  have hprev := st256_p265
  have hstep := st256_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p267 : ((1942417485917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT256 (i+1))
      = (∑ i ∈ Finset.range 266, stT256 (i+1)) + stT256 267 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 266
    simpa using h
  have hprev := st256_p266
  have hstep := st256_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p268 : ((1899825345557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT256 (i+1))
      = (∑ i ∈ Finset.range 267, stT256 (i+1)) + stT256 268 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 267
    simpa using h
  have hprev := st256_p267
  have hstep := st256_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p269 : ((997286987351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT256 (i+1))
      = (∑ i ∈ Finset.range 268, stT256 (i+1)) + stT256 269 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 268
    simpa using h
  have hprev := st256_p268
  have hstep := st256_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p270 : ((536630372623/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT256 (i+1))
      = (∑ i ∈ Finset.range 269, stT256 (i+1)) + stT256 270 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 269
    simpa using h
  have hprev := st256_p269
  have hstep := st256_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p271 : ((557257490253/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT256 (i+1))
      = (∑ i ∈ Finset.range 270, stT256 (i+1)) + stT256 271 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 270
    simpa using h
  have hprev := st256_p270
  have hstep := st256_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p272 : ((543605745153/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT256 (i+1))
      = (∑ i ∈ Finset.range 271, stT256 (i+1)) + stT256 272 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 271
    simpa using h
  have hprev := st256_p271
  have hstep := st256_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p273 : ((2028306567247/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT256 (i+1))
      = (∑ i ∈ Finset.range 272, stT256 (i+1)) + stT256 273 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 272
    simpa using h
  have hprev := st256_p272
  have hstep := st256_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p274 : ((238776801947/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT256 (i+1))
      = (∑ i ∈ Finset.range 273, stT256 (i+1)) + stT256 274 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 273
    simpa using h
  have hprev := st256_p273
  have hstep := st256_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p275 : ((1915473671949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT256 (i+1))
      = (∑ i ∈ Finset.range 274, stT256 (i+1)) + stT256 275 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 274
    simpa using h
  have hprev := st256_p274
  have hstep := st256_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p276 : ((8156395613379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT256 (i+1))
      = (∑ i ∈ Finset.range 275, stT256 (i+1)) + stT256 276 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 275
    simpa using h
  have hprev := st256_p275
  have hstep := st256_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p277 : ((218171166911/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT256 (i+1))
      = (∑ i ∈ Finset.range 276, stT256 (i+1)) + stT256 277 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 276
    simpa using h
  have hprev := st256_p276
  have hstep := st256_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p278 : ((223015278491/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT256 (i+1))
      = (∑ i ∈ Finset.range 277, stT256 (i+1)) + stT256 278 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 277
    simpa using h
  have hprev := st256_p277
  have hstep := st256_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p279 : ((107342647569/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT256 (i+1))
      = (∑ i ∈ Finset.range 278, stT256 (i+1)) + stT256 279 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 278
    simpa using h
  have hprev := st256_p278
  have hstep := st256_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p280 : ((1598203307547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT256 (i+1))
      = (∑ i ∈ Finset.range 279, stT256 (i+1)) + stT256 280 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 279
    simpa using h
  have hprev := st256_p279
  have hstep := st256_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p281 : ((1519271629467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT256 (i+1))
      = (∑ i ∈ Finset.range 280, stT256 (i+1)) + stT256 281 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 280
    simpa using h
  have hprev := st256_p280
  have hstep := st256_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p282 : ((481674236553/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT256 (i+1))
      = (∑ i ∈ Finset.range 281, stT256 (i+1)) + stT256 282 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 281
    simpa using h
  have hprev := st256_p281
  have hstep := st256_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p283 : ((4117280078793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT256 (i+1))
      = (∑ i ∈ Finset.range 282, stT256 (i+1)) + stT256 283 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 282
    simpa using h
  have hprev := st256_p282
  have hstep := st256_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p284 : ((1096892083427/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT256 (i+1))
      = (∑ i ∈ Finset.range 283, stT256 (i+1)) + stT256 284 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 283
    simpa using h
  have hprev := st256_p283
  have hstep := st256_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p285 : ((1742062573/1953125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT256 (i+1))
      = (∑ i ∈ Finset.range 284, stT256 (i+1)) + stT256 285 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 284
    simpa using h
  have hprev := st256_p284
  have hstep := st256_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p286 : ((1712230365611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT256 (i+1))
      = (∑ i ∈ Finset.range 285, stT256 (i+1)) + stT256 286 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 285
    simpa using h
  have hprev := st256_p285
  have hstep := st256_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p287 : ((7971048683501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT256 (i+1))
      = (∑ i ∈ Finset.range 286, stT256 (i+1)) + stT256 287 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 286
    simpa using h
  have hprev := st256_p286
  have hstep := st256_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p288 : ((1517658193377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT256 (i+1))
      = (∑ i ∈ Finset.range 287, stT256 (i+1)) + stT256 288 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 287
    simpa using h
  have hprev := st256_p287
  have hstep := st256_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p289 : ((153876159459/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT256 (i+1))
      = (∑ i ∈ Finset.range 288, stT256 (i+1)) + stT256 289 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 288
    simpa using h
  have hprev := st256_p288
  have hstep := st256_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p290 : ((820738882329/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT256 (i+1))
      = (∑ i ∈ Finset.range 289, stT256 (i+1)) + stT256 290 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 289
    simpa using h
  have hprev := st256_p289
  have hstep := st256_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p291 : ((218820067769/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT256 (i+1))
      = (∑ i ∈ Finset.range 290, stT256 (i+1)) + stT256 291 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 290
    simpa using h
  have hprev := st256_p290
  have hstep := st256_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p292 : ((893542763511/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT256 (i+1))
      = (∑ i ∈ Finset.range 291, stT256 (i+1)) + stT256 292 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 291
    simpa using h
  have hprev := st256_p291
  have hstep := st256_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p293 : ((1078271331147/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT256 (i+1))
      = (∑ i ∈ Finset.range 292, stT256 (i+1)) + stT256 293 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 292
    simpa using h
  have hprev := st256_p292
  have hstep := st256_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p294 : ((1006087473513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT256 (i+1))
      = (∑ i ∈ Finset.range 293, stT256 (i+1)) + stT256 294 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 293
    simpa using h
  have hprev := st256_p293
  have hstep := st256_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p295 : ((7614224607699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT256 (i+1))
      = (∑ i ∈ Finset.range 294, stT256 (i+1)) + stT256 295 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 294
    simpa using h
  have hprev := st256_p294
  have hstep := st256_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p296 : ((7628153976369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT256 (i+1))
      = (∑ i ∈ Finset.range 295, stT256 (i+1)) + stT256 296 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 295
    simpa using h
  have hprev := st256_p295
  have hstep := st256_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p297 : ((8078086609827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT256 (i+1))
      = (∑ i ∈ Finset.range 296, stT256 (i+1)) + stT256 297 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 296
    simpa using h
  have hprev := st256_p296
  have hstep := st256_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p298 : ((8648278168163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT256 (i+1))
      = (∑ i ∈ Finset.range 297, stT256 (i+1)) + stT256 298 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 297
    simpa using h
  have hprev := st256_p297
  have hstep := st256_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p299 : ((8943617923137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT256 (i+1))
      = (∑ i ∈ Finset.range 298, stT256 (i+1)) + stT256 299 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 298
    simpa using h
  have hprev := st256_p298
  have hstep := st256_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p300 : ((8762679583843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT256 (i+1))
      = (∑ i ∈ Finset.range 299, stT256 (i+1)) + stT256 300 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 299
    simpa using h
  have hprev := st256_p299
  have hstep := st256_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p301 : ((8231796958857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT256 (i+1))
      = (∑ i ∈ Finset.range 300, stT256 (i+1)) + stT256 301 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 300
    simpa using h
  have hprev := st256_p300
  have hstep := st256_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p302 : ((7713352140297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT256 (i+1))
      = (∑ i ∈ Finset.range 301, stT256 (i+1)) + stT256 302 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 301
    simpa using h
  have hprev := st256_p301
  have hstep := st256_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p303 : ((1889251081023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT256 (i+1))
      = (∑ i ∈ Finset.range 302, stT256 (i+1)) + stT256 303 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 302
    simpa using h
  have hprev := st256_p302
  have hstep := st256_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p304 : ((1573093816769/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT256 (i+1))
      = (∑ i ∈ Finset.range 303, stT256 (i+1)) + stT256 304 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 303
    simpa using h
  have hprev := st256_p303
  have hstep := st256_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p305 : ((8430524822989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT256 (i+1))
      = (∑ i ∈ Finset.range 304, stT256 (i+1)) + stT256 305 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 304
    simpa using h
  have hprev := st256_p304
  have hstep := st256_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p306 : ((8876505008817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT256 (i+1))
      = (∑ i ∈ Finset.range 305, stT256 (i+1)) + stT256 306 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 305
    simpa using h
  have hprev := st256_p305
  have hstep := st256_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p307 : ((8910560467917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT256 (i+1))
      = (∑ i ∈ Finset.range 306, stT256 (i+1)) + stT256 307 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 306
    simpa using h
  have hprev := st256_p306
  have hstep := st256_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p308 : ((4256373117817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT256 (i+1))
      = (∑ i ∈ Finset.range 307, stT256 (i+1)) + stT256 308 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 307
    simpa using h
  have hprev := st256_p307
  have hstep := st256_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p309 : ((7944124076489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT256 (i+1))
      = (∑ i ∈ Finset.range 308, stT256 (i+1)) + stT256 309 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 308
    simpa using h
  have hprev := st256_p308
  have hstep := st256_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p310 : ((7573071094117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT256 (i+1))
      = (∑ i ∈ Finset.range 309, stT256 (i+1)) + stT256 310 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 309
    simpa using h
  have hprev := st256_p309
  have hstep := st256_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p311 : ((3818385159431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT256 (i+1))
      = (∑ i ∈ Finset.range 310, stT256 (i+1)) + stT256 311 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 310
    simpa using h
  have hprev := st256_p310
  have hstep := st256_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p312 : ((505754116141/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT256 (i+1))
      = (∑ i ∈ Finset.range 311, stT256 (i+1)) + stT256 312 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 311
    simpa using h
  have hprev := st256_p311
  have hstep := st256_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p313 : ((4323924646481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT256 (i+1))
      = (∑ i ∈ Finset.range 312, stT256 (i+1)) + stT256 313 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 312
    simpa using h
  have hprev := st256_p312
  have hstep := st256_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p314 : ((4476501678491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT256 (i+1))
      = (∑ i ∈ Finset.range 313, stT256 (i+1)) + stT256 314 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 313
    simpa using h
  have hprev := st256_p313
  have hstep := st256_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p315 : ((1102200476439/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT256 (i+1))
      = (∑ i ∈ Finset.range 314, stT256 (i+1)) + stT256 315 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 314
    simpa using h
  have hprev := st256_p314
  have hstep := st256_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p316 : ((1041060241163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT256 (i+1))
      = (∑ i ∈ Finset.range 315, stT256 (i+1)) + stT256 316 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 315
    simpa using h
  have hprev := st256_p315
  have hstep := st256_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p317 : ((486911674149/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT256 (i+1))
      = (∑ i ∈ Finset.range 316, stT256 (i+1)) + stT256 317 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 316
    simpa using h
  have hprev := st256_p316
  have hstep := st256_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p318 : ((7535387405679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT256 (i+1))
      = (∑ i ∈ Finset.range 317, stT256 (i+1)) + stT256 318 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 317
    simpa using h
  have hprev := st256_p317
  have hstep := st256_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p319 : ((7717517473819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT256 (i+1))
      = (∑ i ∈ Finset.range 318, stT256 (i+1)) + stT256 319 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 318
    simpa using h
  have hprev := st256_p318
  have hstep := st256_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p320 : ((1644738050071/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT256 (i+1))
      = (∑ i ∈ Finset.range 319, stT256 (i+1)) + stT256 320 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 319
    simpa using h
  have hprev := st256_p319
  have hstep := st256_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p321 : ((1749182830889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT256 (i+1))
      = (∑ i ∈ Finset.range 320, stT256 (i+1)) + stT256 321 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 320
    simpa using h
  have hprev := st256_p320
  have hstep := st256_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p322 : ((8970041335041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT256 (i+1))
      = (∑ i ∈ Finset.range 321, stT256 (i+1)) + stT256 322 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 321
    simpa using h
  have hprev := st256_p321
  have hstep := st256_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p323 : ((8763704847761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT256 (i+1))
      = (∑ i ∈ Finset.range 322, stT256 (i+1)) + stT256 323 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 322
    simpa using h
  have hprev := st256_p322
  have hstep := st256_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p324 : ((8251888882753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT256 (i+1))
      = (∑ i ∈ Finset.range 323, stT256 (i+1)) + stT256 324 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 323
    simpa using h
  have hprev := st256_p323
  have hstep := st256_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p325 : ((309546559437/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT256 (i+1))
      = (∑ i ∈ Finset.range 324, stT256 (i+1)) + stT256 325 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 324
    simpa using h
  have hprev := st256_p324
  have hstep := st256_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p326 : ((7525499690503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT256 (i+1))
      = (∑ i ∈ Finset.range 325, stT256 (i+1)) + stT256 326 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 325
    simpa using h
  have hprev := st256_p325
  have hstep := st256_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p327 : ((7735233061767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT256 (i+1))
      = (∑ i ∈ Finset.range 326, stT256 (i+1)) + stT256 327 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 326
    simpa using h
  have hprev := st256_p326
  have hstep := st256_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p328 : ((2060941448417/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT256 (i+1))
      = (∑ i ∈ Finset.range 327, stT256 (i+1)) + stT256 328 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 327
    simpa using h
  have hprev := st256_p327
  have hstep := st256_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p329 : ((8755881398383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT256 (i+1))
      = (∑ i ∈ Finset.range 328, stT256 (i+1)) + stT256 329 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 328
    simpa using h
  have hprev := st256_p328
  have hstep := st256_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p330 : ((8977609640373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT256 (i+1))
      = (∑ i ∈ Finset.range 329, stT256 (i+1)) + stT256 330 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 329
    simpa using h
  have hprev := st256_p329
  have hstep := st256_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p331 : ((8783974541173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT256 (i+1))
      = (∑ i ∈ Finset.range 330, stT256 (i+1)) + stT256 331 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 330
    simpa using h
  have hprev := st256_p330
  have hstep := st256_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p332 : ((8287069455907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT256 (i+1))
      = (∑ i ∈ Finset.range 331, stT256 (i+1)) + stT256 332 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 331
    simpa using h
  have hprev := st256_p331
  have hstep := st256_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p333 : ((1942212790221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT256 (i+1))
      = (∑ i ∈ Finset.range 332, stT256 (i+1)) + stT256 333 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 332
    simpa using h
  have hprev := st256_p332
  have hstep := st256_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p334 : ((1880028836907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT256 (i+1))
      = (∑ i ∈ Finset.range 333, stT256 (i+1)) + stT256 334 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 333
    simpa using h
  have hprev := st256_p333
  have hstep := st256_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p335 : ((3839073880027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT256 (i+1))
      = (∑ i ∈ Finset.range 334, stT256 (i+1)) + stT256 335 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 334
    simpa using h
  have hprev := st256_p334
  have hstep := st256_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p336 : ((4076549728771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT256 (i+1))
      = (∑ i ∈ Finset.range 335, stT256 (i+1)) + stT256 336 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 335
    simpa using h
  have hprev := st256_p335
  have hstep := st256_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p337 : ((4340669456011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT256 (i+1))
      = (∑ i ∈ Finset.range 336, stT256 (i+1)) + stT256 337 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 336
    simpa using h
  have hprev := st256_p336
  have hstep := st256_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p338 : ((4486449503039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT256 (i+1))
      = (∑ i ∈ Finset.range 337, stT256 (i+1)) + stT256 338 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 337
    simpa using h
  have hprev := st256_p337
  have hstep := st256_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p339 : ((1108752713567/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT256 (i+1))
      = (∑ i ∈ Finset.range 338, stT256 (i+1)) + stT256 339 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 338
    simpa using h
  have hprev := st256_p338
  have hstep := st256_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p340 : ((2107644619763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT256 (i+1))
      = (∑ i ∈ Finset.range 339, stT256 (i+1)) + stT256 340 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 339
    simpa using h
  have hprev := st256_p339
  have hstep := st256_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p341 : ((3946642750329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT256 (i+1))
      = (∑ i ∈ Finset.range 340, stT256 (i+1)) + stT256 341 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 340
    simpa using h
  have hprev := st256_p340
  have hstep := st256_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p342 : ((1509348743989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT256 (i+1))
      = (∑ i ∈ Finset.range 341, stT256 (i+1)) + stT256 342 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 341
    simpa using h
  have hprev := st256_p341
  have hstep := st256_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p343 : ((7574717397737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT256 (i+1))
      = (∑ i ∈ Finset.range 342, stT256 (i+1)) + stT256 343 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 342
    simpa using h
  have hprev := st256_p342
  have hstep := st256_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p344 : ((62190545761/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT256 (i+1))
      = (∑ i ∈ Finset.range 343, stT256 (i+1)) + stT256 344 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 343
    simpa using h
  have hprev := st256_p343
  have hstep := st256_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p345 : ((2124623263203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT256 (i+1))
      = (∑ i ∈ Finset.range 344, stT256 (i+1)) + stT256 345 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 344
    simpa using h
  have hprev := st256_p344
  have hstep := st256_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p346 : ((8906020318947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT256 (i+1))
      = (∑ i ∈ Finset.range 345, stT256 (i+1)) + stT256 346 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 345
    simpa using h
  have hprev := st256_p345
  have hstep := st256_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p347 : ((1794219029187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT256 (i+1))
      = (∑ i ∈ Finset.range 346, stT256 (i+1)) + stT256 347 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 346
    simpa using h
  have hprev := st256_p346
  have hstep := st256_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p348 : ((2165433224709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT256 (i+1))
      = (∑ i ∈ Finset.range 347, stT256 (i+1)) + stT256 348 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 347
    simpa using h
  have hprev := st256_p347
  have hstep := st256_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p349 : ((2034861761089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT256 (i+1))
      = (∑ i ∈ Finset.range 348, stT256 (i+1)) + stT256 349 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 348
    simpa using h
  have hprev := st256_p348
  have hstep := st256_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p350 : ((3836639957321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT256 (i+1))
      = (∑ i ∈ Finset.range 349, stT256 (i+1)) + stT256 350 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 349
    simpa using h
  have hprev := st256_p349
  have hstep := st256_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p351 : ((7500787041077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT256 (i+1))
      = (∑ i ∈ Finset.range 350, stT256 (i+1)) + stT256 351 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 350
    simpa using h
  have hprev := st256_p350
  have hstep := st256_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p352 : ((3853982531389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT256 (i+1))
      = (∑ i ∈ Finset.range 351, stT256 (i+1)) + stT256 352 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 351
    simpa using h
  have hprev := st256_p351
  have hstep := st256_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p353 : ((818828620751/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT256 (i+1))
      = (∑ i ∈ Finset.range 352, stT256 (i+1)) + stT256 353 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 352
    simpa using h
  have hprev := st256_p352
  have hstep := st256_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p354 : ((4349606226349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT256 (i+1))
      = (∑ i ∈ Finset.range 353, stT256 (i+1)) + stT256 354 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 353
    simpa using h
  have hprev := st256_p353
  have hstep := st256_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p355 : ((4492739921989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT256 (i+1))
      = (∑ i ∈ Finset.range 354, stT256 (i+1)) + stT256 355 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 354
    simpa using h
  have hprev := st256_p354
  have hstep := st256_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p356 : ((4453026036921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT256 (i+1))
      = (∑ i ∈ Finset.range 355, stT256 (i+1)) + stT256 356 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 355
    simpa using h
  have hprev := st256_p355
  have hstep := st256_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p357 : ((8502025218897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT256 (i+1))
      = (∑ i ∈ Finset.range 356, stT256 (i+1)) + stT256 357 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 356
    simpa using h
  have hprev := st256_p356
  have hstep := st256_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p358 : ((1594706294729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT256 (i+1))
      = (∑ i ∈ Finset.range 357, stT256 (i+1)) + stT256 358 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 357
    simpa using h
  have hprev := st256_p357
  have hstep := st256_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p359 : ((1515891112877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT256 (i+1))
      = (∑ i ∈ Finset.range 358, stT256 (i+1)) + stT256 359 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 358
    simpa using h
  have hprev := st256_p358
  have hstep := st256_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p360 : ((751066275471/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT256 (i+1))
      = (∑ i ∈ Finset.range 359, stT256 (i+1)) + stT256 360 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 359
    simpa using h
  have hprev := st256_p359
  have hstep := st256_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p361 : ((779874863837/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT256 (i+1))
      = (∑ i ∈ Finset.range 360, stT256 (i+1)) + stT256 361 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 360
    simpa using h
  have hprev := st256_p360
  have hstep := st256_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p362 : ((4151675743147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT256 (i+1))
      = (∑ i ∈ Finset.range 361, stT256 (i+1)) + stT256 362 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 361
    simpa using h
  have hprev := st256_p361
  have hstep := st256_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p363 : ((2195490102389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT256 (i+1))
      = (∑ i ∈ Finset.range 362, stT256 (i+1)) + stT256 363 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 362
    simpa using h
  have hprev := st256_p362
  have hstep := st256_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p364 : ((281466743239/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT256 (i+1))
      = (∑ i ∈ Finset.range 363, stT256 (i+1)) + stT256 364 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 363
    simpa using h
  have hprev := st256_p363
  have hstep := st256_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p365 : ((277282295499/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT256 (i+1))
      = (∑ i ∈ Finset.range 364, stT256 (i+1)) + stT256 365 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 364
    simpa using h
  have hprev := st256_p364
  have hstep := st256_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p366 : ((33780362209/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT256 (i+1))
      = (∑ i ∈ Finset.range 365, stT256 (i+1)) + stT256 366 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 365
    simpa using h
  have hprev := st256_p365
  have hstep := st256_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p367 : ((3962515839703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT256 (i+1))
      = (∑ i ∈ Finset.range 366, stT256 (i+1)) + stT256 367 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 366
    simpa using h
  have hprev := st256_p366
  have hstep := st256_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p368 : ((7555650317641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT256 (i+1))
      = (∑ i ∈ Finset.range 367, stT256 (i+1)) + stT256 368 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 367
    simpa using h
  have hprev := st256_p367
  have hstep := st256_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p369 : ((7507421704121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT256 (i+1))
      = (∑ i ∈ Finset.range 368, stT256 (i+1)) + stT256 369 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 368
    simpa using h
  have hprev := st256_p368
  have hstep := st256_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p370 : ((7800986798621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT256 (i+1))
      = (∑ i ∈ Finset.range 369, stT256 (i+1)) + stT256 370 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 369
    simpa using h
  have hprev := st256_p369
  have hstep := st256_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p371 : ((8299952989019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT256 (i+1))
      = (∑ i ∈ Finset.range 370, stT256 (i+1)) + stT256 371 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 370
    simpa using h
  have hprev := st256_p370
  have hstep := st256_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p372 : ((8775563586869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT256 (i+1))
      = (∑ i ∈ Finset.range 371, stT256 (i+1)) + stT256 372 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 371
    simpa using h
  have hprev := st256_p371
  have hstep := st256_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p373 : ((9011960188109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT256 (i+1))
      = (∑ i ∈ Finset.range 372, stT256 (i+1)) + stT256 373 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 372
    simpa using h
  have hprev := st256_p372
  have hstep := st256_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p374 : ((71228243633/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT256 (i+1))
      = (∑ i ∈ Finset.range 373, stT256 (i+1)) + stT256 374 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 373
    simpa using h
  have hprev := st256_p373
  have hstep := st256_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p375 : ((8500668751201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT256 (i+1))
      = (∑ i ∈ Finset.range 374, stT256 (i+1)) + stT256 375 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 374
    simpa using h
  have hprev := st256_p374
  have hstep := st256_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p376 : ((3992470366369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT256 (i+1))
      = (∑ i ∈ Finset.range 375, stT256 (i+1)) + stT256 376 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 375
    simpa using h
  have hprev := st256_p375
  have hstep := st256_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p377 : ((1896574111009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT256 (i+1))
      = (∑ i ∈ Finset.range 376, stT256 (i+1)) + stT256 377 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 376
    simpa using h
  have hprev := st256_p376
  have hstep := st256_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p378 : ((1870146036219/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT256 (i+1))
      = (∑ i ∈ Finset.range 377, stT256 (i+1)) + stT256 378 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 377
    simpa using h
  have hprev := st256_p377
  have hstep := st256_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p379 : ((482057947021/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT256 (i+1))
      = (∑ i ∈ Finset.range 378, stT256 (i+1)) + stT256 379 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 378
    simpa using h
  have hprev := st256_p378
  have hstep := st256_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p380 : ((511241891231/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT256 (i+1))
      = (∑ i ∈ Finset.range 379, stT256 (i+1)) + stT256 380 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 379
    simpa using h
  have hprev := st256_p379
  have hstep := st256_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p381 : ((8676738450131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT256 (i+1))
      = (∑ i ∈ Finset.range 380, stT256 (i+1)) + stT256 381 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 380
    simpa using h
  have hprev := st256_p380
  have hstep := st256_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p382 : ((359515298771/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT256 (i+1))
      = (∑ i ∈ Finset.range 381, stT256 (i+1)) + stT256 382 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 381
    simpa using h
  have hprev := st256_p381
  have hstep := st256_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p383 : ((4489968643951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT256 (i+1))
      = (∑ i ∈ Finset.range 382, stT256 (i+1)) + stT256 383 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 382
    simpa using h
  have hprev := st256_p382
  have hstep := st256_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p384 : ((4328912451107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT256 (i+1))
      = (∑ i ∈ Finset.range 383, stT256 (i+1)) + stT256 384 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 383
    simpa using h
  have hprev := st256_p383
  have hstep := st256_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p385 : ((4080326287803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT256 (i+1))
      = (∑ i ∈ Finset.range 384, stT256 (i+1)) + stT256 385 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 384
    simpa using h
  have hprev := st256_p384
  have hstep := st256_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p386 : ((192514506107/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT256 (i+1))
      = (∑ i ∈ Finset.range 385, stT256 (i+1)) + stT256 386 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 385
    simpa using h
  have hprev := st256_p385
  have hstep := st256_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p387 : ((7472004517811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT256 (i+1))
      = (∑ i ∈ Finset.range 386, stT256 (i+1)) + stT256 387 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 386
    simpa using h
  have hprev := st256_p386
  have hstep := st256_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p388 : ((1514002970369/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT256 (i+1))
      = (∑ i ∈ Finset.range 387, stT256 (i+1)) + stT256 388 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 387
    simpa using h
  have hprev := st256_p387
  have hstep := st256_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p389 : ((1590399425717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT256 (i+1))
      = (∑ i ∈ Finset.range 388, stT256 (i+1)) + stT256 389 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 388
    simpa using h
  have hprev := st256_p388
  have hstep := st256_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p390 : ((8457421244031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT256 (i+1))
      = (∑ i ∈ Finset.range 389, stT256 (i+1)) + stT256 390 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 389
    simpa using h
  have hprev := st256_p389
  have hstep := st256_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p391 : ((2219031087181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT256 (i+1))
      = (∑ i ∈ Finset.range 390, stT256 (i+1)) + stT256 391 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 390
    simpa using h
  have hprev := st256_p390
  have hstep := st256_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p392 : ((2258936384327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT256 (i+1))
      = (∑ i ∈ Finset.range 391, stT256 (i+1)) + stT256 392 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 391
    simpa using h
  have hprev := st256_p391
  have hstep := st256_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p393 : ((2217989458811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT256 (i+1))
      = (∑ i ∈ Finset.range 392, stT256 (i+1)) + stT256 393 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 392
    simpa using h
  have hprev := st256_p392
  have hstep := st256_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p394 : ((8453194513991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT256 (i+1))
      = (∑ i ∈ Finset.range 393, stT256 (i+1)) + stT256 394 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 393
    simpa using h
  have hprev := st256_p393
  have hstep := st256_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p395 : ((3975449702943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT256 (i+1))
      = (∑ i ∈ Finset.range 394, stT256 (i+1)) + stT256 395 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 394
    simpa using h
  have hprev := st256_p394
  have hstep := st256_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p396 : ((3784338712129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT256 (i+1))
      = (∑ i ∈ Finset.range 395, stT256 (i+1)) + stT256 396 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 395
    simpa using h
  have hprev := st256_p395
  have hstep := st256_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p397 : ((3729919213149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT256 (i+1))
      = (∑ i ∈ Finset.range 396, stT256 (i+1)) + stT256 397 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 396
    simpa using h
  have hprev := st256_p396
  have hstep := st256_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p398 : ((958339810431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT256 (i+1))
      = (∑ i ∈ Finset.range 397, stT256 (i+1)) + stT256 398 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 397
    simpa using h
  have hprev := st256_p397
  have hstep := st256_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p399 : ((4052669224483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT256 (i+1))
      = (∑ i ∈ Finset.range 398, stT256 (i+1)) + stT256 399 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 398
    simpa using h
  have hprev := st256_p398
  have hstep := st256_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p400 : ((4300283224483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT256 (i+1))
      = (∑ i ∈ Finset.range 399, stT256 (i+1)) + stT256 400 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 399
    simpa using h
  have hprev := st256_p399
  have hstep := st256_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p401 : ((895656860311/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT256 (i+1))
      = (∑ i ∈ Finset.range 400, stT256 (i+1)) + stT256 401 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 400
    simpa using h
  have hprev := st256_p400
  have hstep := st256_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p402 : ((36136319849/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT256 (i+1))
      = (∑ i ∈ Finset.range 401, stT256 (i+1)) + stT256 402 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 401
    simpa using h
  have hprev := st256_p401
  have hstep := st256_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p403 : ((176081064217/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT256 (i+1))
      = (∑ i ∈ Finset.range 402, stT256 (i+1)) + stT256 403 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 402
    simpa using h
  have hprev := st256_p402
  have hstep := st256_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p404 : ((8357435877259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT256 (i+1))
      = (∑ i ∈ Finset.range 403, stT256 (i+1)) + stT256 404 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 403
    simpa using h
  have hprev := st256_p403
  have hstep := st256_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p405 : ((7868224448083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT256 (i+1))
      = (∑ i ∈ Finset.range 404, stT256 (i+1)) + stT256 405 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 404
    simpa using h
  have hprev := st256_p404
  have hstep := st256_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p406 : ((7525214217451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT256 (i+1))
      = (∑ i ∈ Finset.range 405, stT256 (i+1)) + stT256 406 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 405
    simpa using h
  have hprev := st256_p405
  have hstep := st256_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p407 : ((7459337583969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT256 (i+1))
      = (∑ i ∈ Finset.range 406, stT256 (i+1)) + stT256 407 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 406
    simpa using h
  have hprev := st256_p406
  have hstep := st256_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p408 : ((7694479436341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT256 (i+1))
      = (∑ i ∈ Finset.range 407, stT256 (i+1)) + stT256 408 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 407
    simpa using h
  have hprev := st256_p407
  have hstep := st256_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p409 : ((8139884343509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT256 (i+1))
      = (∑ i ∈ Finset.range 408, stT256 (i+1)) + stT256 409 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 408
    simpa using h
  have hprev := st256_p408
  have hstep := st256_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p410 : ((8626092463781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT256 (i+1))
      = (∑ i ∈ Finset.range 409, stT256 (i+1)) + stT256 410 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 409
    simpa using h
  have hprev := st256_p409
  have hstep := st256_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p411 : ((2242461492173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT256 (i+1))
      = (∑ i ∈ Finset.range 410, stT256 (i+1)) + stT256 411 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 410
    simpa using h
  have hprev := st256_p410
  have hstep := st256_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p412 : ((2260742405723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT256 (i+1))
      = (∑ i ∈ Finset.range 411, stT256 (i+1)) + stT256 412 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 411
    simpa using h
  have hprev := st256_p411
  have hstep := st256_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p413 : ((551212869257/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT256 (i+1))
      = (∑ i ∈ Finset.range 412, stT256 (i+1)) + stT256 413 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 412
    simpa using h
  have hprev := st256_p412
  have hstep := st256_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p414 : ((4191736446689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT256 (i+1))
      = (∑ i ∈ Finset.range 413, stT256 (i+1)) + stT256 414 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 413
    simpa using h
  have hprev := st256_p413
  have hstep := st256_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p415 : ((7897200775087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT256 (i+1))
      = (∑ i ∈ Finset.range 414, stT256 (i+1)) + stT256 415 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 414
    simpa using h
  have hprev := st256_p414
  have hstep := st256_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p416 : ((7539649199263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT256 (i+1))
      = (∑ i ∈ Finset.range 415, stT256 (i+1)) + stT256 416 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 415
    simpa using h
  have hprev := st256_p415
  have hstep := st256_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p417 : ((930141037651/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT256 (i+1))
      = (∑ i ∈ Finset.range 416, stT256 (i+1)) + stT256 417 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 416
    simpa using h
  have hprev := st256_p416
  have hstep := st256_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p418 : ((59659089411/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT256 (i+1))
      = (∑ i ∈ Finset.range 417, stT256 (i+1)) + stT256 418 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 417
    simpa using h
  have hprev := st256_p417
  have hstep := st256_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p419 : ((8053224504253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT256 (i+1))
      = (∑ i ∈ Finset.range 418, stT256 (i+1)) + stT256 419 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 418
    simpa using h
  have hprev := st256_p418
  have hstep := st256_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p420 : ((8540218122253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT256 (i+1))
      = (∑ i ∈ Finset.range 419, stT256 (i+1)) + stT256 420 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 419
    simpa using h
  have hprev := st256_p419
  have hstep := st256_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p421 : ((8922017931813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT256 (i+1))
      = (∑ i ∈ Finset.range 420, stT256 (i+1)) + stT256 421 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 420
    simpa using h
  have hprev := st256_p420
  have hstep := st256_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p422 : ((9062507076597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT256 (i+1))
      = (∑ i ∈ Finset.range 421, stT256 (i+1)) + stT256 422 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 421
    simpa using h
  have hprev := st256_p421
  have hstep := st256_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p423 : ((8912731819483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT256 (i+1))
      = (∑ i ∈ Finset.range 422, stT256 (i+1)) + stT256 423 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 422
    simpa using h
  have hprev := st256_p422
  have hstep := st256_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p424 : ((8527043861743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT256 (i+1))
      = (∑ i ∈ Finset.range 423, stT256 (i+1)) + stT256 424 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 423
    simpa using h
  have hprev := st256_p423
  have hstep := st256_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p425 : ((8042557828719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT256 (i+1))
      = (∑ i ∈ Finset.range 424, stT256 (i+1)) + stT256 425 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 424
    simpa using h
  have hprev := st256_p424
  have hstep := st256_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p426 : ((7629860963127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT256 (i+1))
      = (∑ i ∈ Finset.range 425, stT256 (i+1)) + stT256 426 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 425
    simpa using h
  have hprev := st256_p425
  have hstep := st256_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p427 : ((7432921118223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT256 (i+1))
      = (∑ i ∈ Finset.range 426, stT256 (i+1)) + stT256 427 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 426
    simpa using h
  have hprev := st256_p426
  have hstep := st256_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p428 : ((7519312514127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT256 (i+1))
      = (∑ i ∈ Finset.range 427, stT256 (i+1)) + stT256 428 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 427
    simpa using h
  have hprev := st256_p427
  have hstep := st256_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p429 : ((7857871094263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT256 (i+1))
      = (∑ i ∈ Finset.range 428, stT256 (i+1)) + stT256 429 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 428
    simpa using h
  have hprev := st256_p428
  have hstep := st256_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p430 : ((8330709375263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT256 (i+1))
      = (∑ i ∈ Finset.range 429, stT256 (i+1)) + stT256 430 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 429
    simpa using h
  have hprev := st256_p429
  have hstep := st256_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p431 : ((2193722495483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT256 (i+1))
      = (∑ i ∈ Finset.range 430, stT256 (i+1)) + stT256 431 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 430
    simpa using h
  have hprev := st256_p430
  have hstep := st256_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p432 : ((9038708621057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT256 (i+1))
      = (∑ i ∈ Finset.range 431, stT256 (i+1)) + stT256 432 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 431
    simpa using h
  have hprev := st256_p431
  have hstep := st256_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p433 : ((9033163323827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT256 (i+1))
      = (∑ i ∈ Finset.range 432, stT256 (i+1)) + stT256 433 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 432
    simpa using h
  have hprev := st256_p432
  have hstep := st256_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p434 : ((1752259620391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT256 (i+1))
      = (∑ i ∈ Finset.range 433, stT256 (i+1)) + stT256 434 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 433
    simpa using h
  have hprev := st256_p433
  have hstep := st256_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p435 : ((332637535051/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT256 (i+1))
      = (∑ i ∈ Finset.range 434, stT256 (i+1)) + stT256 435 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 434
    simpa using h
  have hprev := st256_p434
  have hstep := st256_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p436 : ((1569469473509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT256 (i+1))
      = (∑ i ∈ Finset.range 435, stT256 (i+1)) + stT256 436 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 435
    simpa using h
  have hprev := st256_p435
  have hstep := st256_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p437 : ((300489380287/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT256 (i+1))
      = (∑ i ∈ Finset.range 436, stT256 (i+1)) + stT256 437 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 436
    simpa using h
  have hprev := st256_p436
  have hstep := st256_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p438 : ((7421540638423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT256 (i+1))
      = (∑ i ∈ Finset.range 437, stT256 (i+1)) + stT256 438 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 437
    simpa using h
  have hprev := st256_p437
  have hstep := st256_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p439 : ((7604246470099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT256 (i+1))
      = (∑ i ∈ Finset.range 438, stT256 (i+1)) + stT256 439 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 438
    simpa using h
  have hprev := st256_p438
  have hstep := st256_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p440 : ((1999728129757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT256 (i+1))
      = (∑ i ∈ Finset.range 439, stT256 (i+1)) + stT256 440 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 439
    simpa using h
  have hprev := st256_p439
  have hstep := st256_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p441 : ((2118757534537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT256 (i+1))
      = (∑ i ∈ Finset.range 440, stT256 (i+1)) + stT256 441 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 440
    simpa using h
  have hprev := st256_p440
  have hstep := st256_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p442 : ((8876593262737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT256 (i+1))
      = (∑ i ∈ Finset.range 441, stT256 (i+1)) + stT256 442 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 441
    simpa using h
  have hprev := st256_p441
  have hstep := st256_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p443 : ((1814641177689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT256 (i+1))
      = (∑ i ∈ Finset.range 442, stT256 (i+1)) + stT256 443 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 442
    simpa using h
  have hprev := st256_p442
  have hstep := st256_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p444 : ((1125251964549/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT256 (i+1))
      = (∑ i ∈ Finset.range 443, stT256 (i+1)) + stT256 444 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 443
    simpa using h
  have hprev := st256_p443
  have hstep := st256_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p445 : ((4343560827009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT256 (i+1))
      = (∑ i ∈ Finset.range 444, stT256 (i+1)) + stT256 445 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 444
    simpa using h
  have hprev := st256_p444
  have hstep := st256_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p446 : ((4115350754709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT256 (i+1))
      = (∑ i ∈ Finset.range 445, stT256 (i+1)) + stT256 446 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 445
    simpa using h
  have hprev := st256_p445
  have hstep := st256_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p447 : ((777932956733/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT256 (i+1))
      = (∑ i ∈ Finset.range 446, stT256 (i+1)) + stT256 447 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 446
    simpa using h
  have hprev := st256_p446
  have hstep := st256_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p448 : ((3738361458349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT256 (i+1))
      = (∑ i ∈ Finset.range 447, stT256 (i+1)) + stT256 448 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 447
    simpa using h
  have hprev := st256_p447
  have hstep := st256_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p449 : ((231818375719/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT256 (i+1))
      = (∑ i ∈ Finset.range 448, stT256 (i+1)) + stT256 449 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 448
    simpa using h
  have hprev := st256_p448
  have hstep := st256_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p450 : ((1905294471309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT256 (i+1))
      = (∑ i ∈ Finset.range 449, stT256 (i+1)) + stT256 450 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 449
    simpa using h
  have hprev := st256_p449
  have hstep := st256_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p451 : ((8020783040909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT256 (i+1))
      = (∑ i ∈ Finset.range 450, stT256 (i+1)) + stT256 451 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 450
    simpa using h
  have hprev := st256_p450
  have hstep := st256_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p452 : ((8491097415989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT256 (i+1))
      = (∑ i ∈ Finset.range 451, stT256 (i+1)) + stT256 452 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 451
    simpa using h
  have hprev := st256_p451
  have hstep := st256_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p453 : ((8885247131669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT256 (i+1))
      = (∑ i ∈ Finset.range 452, stT256 (i+1)) + stT256 453 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 452
    simpa using h
  have hprev := st256_p452
  have hstep := st256_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p454 : ((4540621728157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT256 (i+1))
      = (∑ i ∈ Finset.range 453, stT256 (i+1)) + stT256 454 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 453
    simpa using h
  have hprev := st256_p453
  have hstep := st256_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p455 : ((4509664929493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT256 (i+1))
      = (∑ i ∈ Finset.range 454, stT256 (i+1)) + stT256 455 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 454
    simpa using h
  have hprev := st256_p454
  have hstep := st256_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p456 : ((1089953143593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT256 (i+1))
      = (∑ i ∈ Finset.range 455, stT256 (i+1)) + stT256 456 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 455
    simpa using h
  have hprev := st256_p455
  have hstep := st256_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p457 : ((1654984986213/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT256 (i+1))
      = (∑ i ∈ Finset.range 456, stT256 (i+1)) + stT256 457 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 456
    simpa using h
  have hprev := st256_p456
  have hstep := st256_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p458 : ((1564293579907/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT256 (i+1))
      = (∑ i ∈ Finset.range 457, stT256 (i+1)) + stT256 458 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 457
    simpa using h
  have hprev := st256_p457
  have hstep := st256_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p459 : ((7497027929567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT256 (i+1))
      = (∑ i ∈ Finset.range 458, stT256 (i+1)) + stT256 459 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 458
    simpa using h
  have hprev := st256_p458
  have hstep := st256_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p460 : ((7399186602529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT256 (i+1))
      = (∑ i ∈ Finset.range 459, stT256 (i+1)) + stT256 460 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 459
    simpa using h
  have hprev := st256_p459
  have hstep := st256_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p461 : ((1511297158717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT256 (i+1))
      = (∑ i ∈ Finset.range 460, stT256 (i+1)) + stT256 461 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 460
    simpa using h
  have hprev := st256_p460
  have hstep := st256_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p462 : ((7920686070783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT256 (i+1))
      = (∑ i ∈ Finset.range 461, stT256 (i+1)) + stT256 462 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 461
    simpa using h
  have hprev := st256_p461
  have hstep := st256_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p463 : ((1047771196761/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT256 (i+1))
      = (∑ i ∈ Finset.range 462, stT256 (i+1)) + stT256 463 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 462
    simpa using h
  have hprev := st256_p462
  have hstep := st256_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p464 : ((2200821126567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT256 (i+1))
      = (∑ i ∈ Finset.range 463, stT256 (i+1)) + stT256 464 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 463
    simpa using h
  have hprev := st256_p463
  have hstep := st256_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p465 : ((4529734804149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT256 (i+1))
      = (∑ i ∈ Finset.range 464, stT256 (i+1)) + stT256 465 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 464
    simpa using h
  have hprev := st256_p464
  have hstep := st256_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p466 : ((2268960831171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT256 (i+1))
      = (∑ i ∈ Finset.range 465, stT256 (i+1)) + stT256 466 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 465
    simpa using h
  have hprev := st256_p465
  have hstep := st256_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p467 : ((8848563804209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT256 (i+1))
      = (∑ i ∈ Finset.range 466, stT256 (i+1)) + stT256 467 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 466
    simpa using h
  have hprev := st256_p466
  have hstep := st256_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p468 : ((8445080622843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT256 (i+1))
      = (∑ i ∈ Finset.range 467, stT256 (i+1)) + stT256 468 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 467
    simpa using h
  have hprev := st256_p467
  have hstep := st256_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p469 : ((1596721690209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT256 (i+1))
      = (∑ i ∈ Finset.range 468, stT256 (i+1)) + stT256 469 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 468
    simpa using h
  have hprev := st256_p468
  have hstep := st256_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p470 : ((7598217479183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT256 (i+1))
      = (∑ i ∈ Finset.range 469, stT256 (i+1)) + stT256 470 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 469
    simpa using h
  have hprev := st256_p469
  have hstep := st256_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p471 : ((295996292879/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT256 (i+1))
      = (∑ i ∈ Finset.range 470, stT256 (i+1)) + stT256 471 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 470
    simpa using h
  have hprev := st256_p470
  have hstep := st256_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p472 : ((3722480336911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT256 (i+1))
      = (∑ i ∈ Finset.range 471, stT256 (i+1)) + stT256 472 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 471
    simpa using h
  have hprev := st256_p471
  have hstep := st256_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p473 : ((3859743281411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT256 (i+1))
      = (∑ i ∈ Finset.range 472, stT256 (i+1)) + stT256 473 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 472
    simpa using h
  have hprev := st256_p472
  have hstep := st256_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p474 : ((8144246836057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT256 (i+1))
      = (∑ i ∈ Finset.range 473, stT256 (i+1)) + stT256 474 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 473
    simpa using h
  have hprev := st256_p473
  have hstep := st256_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p475 : ((68783614209/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT256 (i+1))
      = (∑ i ∈ Finset.range 474, stT256 (i+1)) + stT256 475 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 474
    simpa using h
  have hprev := st256_p474
  have hstep := st256_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p476 : ((4476056503293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT256 (i+1))
      = (∑ i ∈ Finset.range 475, stT256 (i+1)) + stT256 476 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 475
    simpa using h
  have hprev := st256_p475
  have hstep := st256_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p477 : ((182146586857/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT256 (i+1))
      = (∑ i ∈ Finset.range 476, stT256 (i+1)) + stT256 477 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 476
    simpa using h
  have hprev := st256_p476
  have hstep := st256_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p478 : ((451040907043/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT256 (i+1))
      = (∑ i ∈ Finset.range 477, stT256 (i+1)) + stT256 478 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 477
    simpa using h
  have hprev := st256_p477
  have hstep := st256_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p479 : ((2179430934503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT256 (i+1))
      = (∑ i ∈ Finset.range 478, stT256 (i+1)) + stT256 479 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 478
    simpa using h
  have hprev := st256_p478
  have hstep := st256_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p480 : ((207081320191/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT256 (i+1))
      = (∑ i ∈ Finset.range 479, stT256 (i+1)) + stT256 480 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 479
    simpa using h
  have hprev := st256_p479
  have hstep := st256_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p481 : ((3919184462087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT256 (i+1))
      = (∑ i ∈ Finset.range 480, stT256 (i+1)) + stT256 481 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 480
    simpa using h
  have hprev := st256_p480
  have hstep := st256_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p482 : ((3752969147591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT256 (i+1))
      = (∑ i ∈ Finset.range 481, stT256 (i+1)) + stT256 482 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 481
    simpa using h
  have hprev := st256_p481
  have hstep := st256_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p483 : ((3688458344159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT256 (i+1))
      = (∑ i ∈ Finset.range 482, stT256 (i+1)) + stT256 483 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 482
    simpa using h
  have hprev := st256_p482
  have hstep := st256_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p484 : ((7485840670303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT256 (i+1))
      = (∑ i ∈ Finset.range 483, stT256 (i+1)) + stT256 484 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 483
    simpa using h
  have hprev := st256_p483
  have hstep := st256_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p485 : ((7802046028499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT256 (i+1))
      = (∑ i ∈ Finset.range 484, stT256 (i+1)) + stT256 485 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 484
    simpa using h
  have hprev := st256_p484
  have hstep := st256_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p486 : ((8238822505727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT256 (i+1))
      = (∑ i ∈ Finset.range 485, stT256 (i+1)) + stT256 486 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 485
    simpa using h
  have hprev := st256_p485
  have hstep := st256_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p487 : ((347100156001/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT256 (i+1))
      = (∑ i ∈ Finset.range 486, stT256 (i+1)) + stT256 487 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 486
    simpa using h
  have hprev := st256_p486
  have hstep := st256_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p488 : ((8999852735079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT256 (i+1))
      = (∑ i ∈ Finset.range 487, stT256 (i+1)) + stT256 488 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 487
    simpa using h
  have hprev := st256_p487
  have hstep := st256_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p489 : ((4559901155807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT256 (i+1))
      = (∑ i ∈ Finset.range 488, stT256 (i+1)) + stT256 489 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 488
    simpa using h
  have hprev := st256_p488
  have hstep := st256_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p490 : ((450302961887/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT256 (i+1))
      = (∑ i ∈ Finset.range 489, stT256 (i+1)) + stT256 490 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 489
    simpa using h
  have hprev := st256_p489
  have hstep := st256_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p491 : ((4344903647621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT256 (i+1))
      = (∑ i ∈ Finset.range 490, stT256 (i+1)) + stT256 491 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 490
    simpa using h
  have hprev := st256_p490
  have hstep := st256_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p492 : ((8255711347957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT256 (i+1))
      = (∑ i ∈ Finset.range 491, stT256 (i+1)) + stT256 492 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 491
    simpa using h
  have hprev := st256_p491
  have hstep := st256_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p493 : ((1563779386361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT256 (i+1))
      = (∑ i ∈ Finset.range 492, stT256 (i+1)) + stT256 493 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 492
    simpa using h
  have hprev := st256_p492
  have hstep := st256_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p494 : ((1498861940669/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT256 (i+1))
      = (∑ i ∈ Finset.range 493, stT256 (i+1)) + stT256 494 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 493
    simpa using h
  have hprev := st256_p493
  have hstep := st256_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p495 : ((1473315135323/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT256 (i+1))
      = (∑ i ∈ Finset.range 494, stT256 (i+1)) + stT256 495 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 494
    simpa using h
  have hprev := st256_p494
  have hstep := st256_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p496 : ((746828385631/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT256 (i+1))
      = (∑ i ∈ Finset.range 495, stT256 (i+1)) + stT256 496 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 495
    simpa using h
  have hprev := st256_p495
  have hstep := st256_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p497 : ((3886048007927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT256 (i+1))
      = (∑ i ∈ Finset.range 496, stT256 (i+1)) + stT256 497 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 496
    simpa using h
  have hprev := st256_p496
  have hstep := st256_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p498 : ((4099269500567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT256 (i+1))
      = (∑ i ∈ Finset.range 497, stT256 (i+1)) + stT256 498 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 497
    simpa using h
  have hprev := st256_p497
  have hstep := st256_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p499 : ((431856206101/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT256 (i+1))
      = (∑ i ∈ Finset.range 498, stT256 (i+1)) + stT256 499 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 498
    simpa using h
  have hprev := st256_p498
  have hstep := st256_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_p500 : ((8975090588741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT256 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT256 (i+1))
      = (∑ i ∈ Finset.range 499, stT256 (i+1)) + stT256 500 := by
    have h := Finset.sum_range_succ (fun i => stT256 (i+1)) 499
    simpa using h
  have hprev := st256_p499
  have hstep := st256_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st256_s500 :
    |Real.sin (((256 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))
      - ((16371/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 55779/312500) (δ := 6459/500000000) (ψ := 579807/1000000) 256 253
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 256`** (evaluated boundary). -/
theorem station_256_sign : 0 < hardyG ((((256:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 256 500 (by norm_num) (by norm_num)
    ((579807/1000000 : ℚ) : ℝ)
  have hchain := st256_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT256 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((256 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((579807/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st256_c500
  have hsinb := abs_le.mp st256_s500
  have hbdy_lo : ((-75145255945679/1310725000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((256 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((579807/1000000 : ℚ) : ℝ))) / 2
          - ((((256:ℕ)):ℝ))
            * Real.sin (((256 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((579807/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((256:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((256:ℝ) * Real.log (500:ℝ) - ((579807/1000000 : ℚ) : ℝ))) / 2
        - ((256:ℝ)) * Real.sin ((256:ℝ) * Real.log (500:ℝ) - ((579807/1000000 : ℚ) : ℝ))
        ≥ ((-336059497/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((256:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-336059497/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-336059497/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-336059497/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((256:ℕ)):ℝ))+1) * (((((256:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2590297699871/5000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8975090588741/10000000000000 : ℚ) : ℝ) + ((-75145255945679/1310725000000000 : ℚ) : ℝ)
      - ((2590297699871/5000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((579807/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((256:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((579807/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((256:ℕ)):ℝ)))).re
      - Real.sin ((579807/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((256:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((256:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((256:ℕ)):ℝ))
      = (((((256:ℕ)):ℝ)) * (Real.log ((((256:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((256:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_256
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
  have hθwin : |(((579807/1000000 : ℚ) : ℝ) + ((55:ℤ)) * (2*Real.pi)) - theta ((((256:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((256:ℕ)):ℝ)))
    (φ := ((579807/1000000 : ℚ) : ℝ) + ((55:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((579807/1000000 : ℚ)) : ℝ) 55).1,
    (cos_sin_shift (((579807/1000000 : ℚ)) : ℝ) 55).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_256_sign
end AxiomAudit
